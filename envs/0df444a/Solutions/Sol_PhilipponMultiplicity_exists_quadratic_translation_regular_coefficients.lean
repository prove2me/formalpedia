-- Prove2me | solution 1 for PhilipponMultiplicity.exists_quadratic_translation_regular_coefficients
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T23:24:24.629979+00:00
-- url     : https://prove2.me/submissions/4d98c22c-123b-4a1e-a990-040251d4b2fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_quadratic_homogeneous_translation_families
import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib


section

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.HomogeneousNormalization
universe u v w
variable {R : Type u} [CommSemiring R] {K : Type v} [Field K]
  {σ : Type w} [Fintype σ]

/-- Scaling variables in a form over an arbitrary coefficient ring. -/
theorem eval₂_scale (φ : R →+* K) (P : MvPolynomial σ R) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j, m j = d) (v : σ → K) (a : K) :
    eval₂ φ (fun j => a * v j) P = a ^ d * eval₂ φ v P := by
  classical
  simp only [eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hP m hm]
  ring

theorem eval₂_normalize (φ : R →+* K) (P : MvPolynomial σ R) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j, m j = d) (v : σ → K) (c : σ) :
    eval₂ φ (fun j => v j / v c) P = (v c)⁻¹ ^ d * eval₂ φ v P := by
  simpa only [div_eq_mul_inv, mul_comm] using eval₂_scale φ P d hP v (v c)⁻¹

/-- A homogeneous fraction of equal numerator/denominator degree is chart invariant. -/
theorem fraction_normalize (A B : MvPolynomial σ K) (d : ℕ)
    (hA : ∀ m ∈ A.support, ∑ j, m j = d)
    (hB : ∀ m ∈ B.support, ∑ j, m j = d)
    (v : σ → K) (c : σ) (hc : v c ≠ 0) (hden : eval v B ≠ 0) :
    eval (fun j => v j / v c) B ≠ 0 ∧
      eval (fun j => v j / v c) A / eval (fun j => v j / v c) B =
        eval v A / eval v B := by
  have hs : (v c)⁻¹ ^ d ≠ 0 := pow_ne_zero _ (inv_ne_zero hc)
  have hAs := eval₂_normalize (RingHom.id K) A d hA v c
  have hBs := eval₂_normalize (RingHom.id K) B d hB v c
  change eval (fun j => v j / v c) A = _ at hAs
  change eval (fun j => v j / v c) B = _ at hBs
  rw [hAs, hBs]
  exact ⟨mul_ne_zero hs hden, mul_div_mul_left _ _ hs⟩

/-- Normalizing the input of a tuple of equal-degree forms preserves its projective value. -/
theorem projective_normalize {ι : Type*} (φ : R →+* K)
    (P : ι → MvPolynomial σ R) (d : ℕ)
    (hP : ∀ t, ∀ m ∈ (P t).support, ∑ j, m j = d)
    (v : σ → K) (c : σ) (hc : v c ≠ 0)
    (hn : (fun t => eval₂ φ v (P t)) ≠ 0) :
    ∃ hn' : (fun t => eval₂ φ (fun j => v j / v c) (P t)) ≠ 0,
      Projectivization.mk K (fun t => eval₂ φ (fun j => v j / v c) (P t)) hn' =
        Projectivization.mk K (fun t => eval₂ φ v (P t)) hn := by
  have hs : (v c)⁻¹ ^ d ≠ 0 := pow_ne_zero _ (inv_ne_zero hc)
  have heq : (fun t => eval₂ φ (fun j => v j / v c) (P t)) =
      ((v c)⁻¹ ^ d) • (fun t => eval₂ φ v (P t)) := by
    funext t
    exact eval₂_normalize φ (P t) d (hP t) v c
  have hn' : (fun t => eval₂ φ (fun j => v j / v c) (P t)) ≠ 0 := by
    rw [heq]
    exact smul_ne_zero hs hn
  refine ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ?_⟩
  exact ⟨(v c)⁻¹ ^ d, heq.symm⟩

def parameterPullback (X : Type*) : (X → K) →+* ((X × X) → K) :=
  RingHom.pi (fun xy : X × X => Pi.evalRingHom (fun _ : X => K) xy.2)

@[simp] theorem parameterPullback_apply (X : Type*) (f : X → K) (xy : X × X) :
    parameterPullback X f xy = f xy.2 := rfl

theorem pullback_degree (X : Type*) (P : MvPolynomial σ (X → K)) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j, m j = d) :
    ∀ m ∈ (map (parameterPullback X) P).support, ∑ j, m j = d := by
  intro m hm
  exact hP m (support_map_subset _ _ hm)

@[simp] theorem pullback_coeff (X : Type*) (P : MvPolynomial σ (X → K))
    (m : σ →₀ ℕ) (xy : X × X) :
    (map (parameterPullback X) P).coeff m xy = P.coeff m xy.2 := by
  rw [coeff_map]
  rfl

@[simp] theorem pullback_eval (X : Type*) (P : MvPolynomial σ (X → K))
    (xy : X × X) (v : σ → K) :
    eval₂ (Pi.evalRingHom (fun _ : X × X => K) xy) v (map (parameterPullback X) P) =
      eval₂ (Pi.evalRingHom (fun _ : X => K) xy.2) v P := by
  rw [eval₂_map]
  rfl

end PhilipponMultiplicity.HomogeneousNormalization
end
end


section
set_option autoImplicit false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section
namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

/-- Every point of an induced multiprojective topology has a simultaneous pivot chart. -/
theorem exists_pivot_neighborhood {X : Type*} (e : X → M.Point) (x : X) :
    ∃ (c : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) (U : Set X),
      @IsOpen _ (TopologicalSpace.induced e M.zariskiTopology) U ∧ x ∈ U ∧
      ∀ z ∈ U, ∀ i, M.coordinate (e z) ⟨i,c i⟩ ≠ 0 := by
  classical
  letI := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  have hex (i : M.FactorIndex) : ∃ j, M.coordinate (e x) ⟨i,j⟩ ≠ 0 := by
    simpa only [coordinate, ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall]
      using (e x i).rep_nonzero
  choose c hc using hex
  let U : Set X := ⋂ i, {z | M.coordinate (e z) ⟨i,c i⟩ ≠ 0}
  refine ⟨c, U, ?_, ?_, ?_⟩
  · apply isOpen_iInter_of_finite
    intro i
    have h := (M.isOpen_basic (MvPolynomial.X ⟨i,c i⟩) _
      (M.isHomogeneous_X ⟨i,c i⟩)).preimage (continuous_induced_dom (f := e))
    simpa only [Set.preimage_setOf_eq, eval, MvPolynomial.eval_X] using h
  · exact Set.mem_iInter.mpr hc
  · intro z hz i
    exact Set.mem_iInter.mp hz i

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section
namespace PhilipponMultiplicity
open HomogeneousNormalization

theorem regular_coefficients_of_homogeneous_families
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (hgeometry : ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ P : Fin (F.ambientDimension+1) →
              MvPolynomial (Fin (F.ambientDimension+1)) (F.Point → K),
          (∀ t, ∀ m ∈ (P t).support, (∑ j, m j) = 2) ∧
          (∀ t, ∀ m ∈ (P t).support, ∀ xy ∈ U,
            ∃ V : Set (F.Point × F.Point),
              @IsOpen _ (TopologicalSpace.induced (fun zw => F.additionPair zw.1 zw.2)
                (projectiveSquare K F.ambientDimension).zariskiTopology) V ∧ xy ∈ V ∧
              ∃ (d : ℕ) (A B : MvPolynomial (Fin (F.ambientDimension+1)) K),
                (∀ a ∈ A.support, (∑ j, a j) = d) ∧
                (∀ a ∈ B.support, (∑ j, a j) = d) ∧
                ∀ zw ∈ U ∩ V,
                  MvPolynomial.eval zw.2.val.rep B ≠ 0 ∧
                    (P t).coeff m zw.2 = MvPolynomial.eval zw.2.val.rep A /
                      MvPolynomial.eval zw.2.val.rep B) ∧
          ∀ xy ∈ U,
            ∃ h : (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point => K) xy.2) xy.1.val.rep (P t)) ≠ 0,
              Projectivization.mk K (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point => K) xy.2) xy.1.val.rep (P t)) h =
                  (xy.1+xy.2).val) :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ c : (projectiveSquare K F.ambientDimension).FactorIndex →
              Fin (F.ambientDimension+1),
          (∀ xy ∈ U, ∀ i : (projectiveSquare K F.ambientDimension).FactorIndex,
            (projectiveSquare K F.ambientDimension).coordinate
              (F.additionPair xy.1 xy.2) ⟨i,c i⟩ ≠ 0) ∧
          ∃ P : Fin (F.ambientDimension+1) →
              MvPolynomial (Fin (F.ambientDimension+1)) ((F.Point × F.Point) → K),
          (∀ t, ∀ m ∈ (P t).support, (∑ j, m j) ≤ 2) ∧
          (∀ t, ∀ m ∈ (P t).support, ∀ xy ∈ U,
            ∃ V : Set (F.Point × F.Point),
              @IsOpen _ (TopologicalSpace.induced (fun zw => F.additionPair zw.1 zw.2)
                (projectiveSquare K F.ambientDimension).zariskiTopology) V ∧ xy ∈ V ∧
              ∃ A B : MvPolynomial (Fin (F.ambientDimension+1)) K,
                ∀ zw ∈ U ∩ V,
                  let w : Fin (F.ambientDimension+1) → K := fun j =>
                    (projectiveSquare K F.ambientDimension).coordinate
                      (F.additionPair zw.1 zw.2) ⟨(1 : Fin 2),j⟩ /
                    (projectiveSquare K F.ambientDimension).coordinate
                      (F.additionPair zw.1 zw.2) ⟨(1 : Fin 2),c (1 : Fin 2)⟩
                  MvPolynomial.eval w B ≠ 0 ∧
                    (P t).coeff m zw = MvPolynomial.eval w A / MvPolynomial.eval w B) ∧
          ∀ xy ∈ U,
            let w : Fin (F.ambientDimension+1) → K := fun j =>
              (projectiveSquare K F.ambientDimension).coordinate
                (F.additionPair xy.1 xy.2) ⟨(0 : Fin 2),j⟩ /
              (projectiveSquare K F.ambientDimension).coordinate
                (F.additionPair xy.1 xy.2) ⟨(0 : Fin 2),c (0 : Fin 2)⟩
            ∃ h : (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point × F.Point => K) xy) w (P t)) ≠ 0,
              Projectivization.mk K (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point × F.Point => K) xy) w (P t)) h =
                  (xy.1+xy.2).val := by
  intro E hE
  obtain ⟨F, hF, hfamily⟩ := hgeometry E hE
  refine ⟨F, hF, ?_⟩
  intro x y
  let M := projectiveSquare K F.ambientDimension
  letI : TopologicalSpace (F.Point × F.Point) :=
    TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2) M.zariskiTopology
  obtain ⟨U, hU, hxyU, P, hP, hcoeff, hrep⟩ := hfamily x y
  obtain ⟨c, V, hV, hxyV, hpivot⟩ :=
    M.exists_pivot_neighborhood (fun xy : F.Point × F.Point => F.additionPair xy.1 xy.2) (x,y)
  let Q := fun t => map (parameterPullback F.Point) (P t)
  refine ⟨U ∩ V, hU.inter hV, ⟨hxyU,hxyV⟩, c, ?_, Q, ?_, ?_, ?_⟩
  · intro xy hxy i
    exact hpivot xy hxy.2 i
  · intro t m hm
    exact le_of_eq (pullback_degree F.Point (P t) 2 (hP t) m hm)
  · intro t m hm xy hxy
    have hm' : m ∈ (P t).support := support_map_subset _ _ hm
    obtain ⟨W,hW,hxyW,d,A,B,hA,hB,hfrac⟩ := hcoeff t m hm' xy hxy.1
    refine ⟨W,hW,hxyW,A,B,?_⟩
    intro zw hzw
    obtain ⟨hden,heq⟩ := hfrac zw ⟨hzw.1.1,hzw.2⟩
    have hc : zw.2.val.rep (c (1 : Fin 2)) ≠ 0 := by
      simpa [M, MultiProjectiveSpace.coordinate, EmbeddedCommutativeGroup.additionPair,
        projectiveSquare] using hpivot zw hzw.1.2 (1 : Fin 2)
    obtain ⟨hden',heval⟩ := fraction_normalize A B d hA hB zw.2.val.rep (c (1 : Fin 2)) hc hden
    change eval (fun j => zw.2.val.rep j / zw.2.val.rep (c (1 : Fin 2))) B ≠ 0 ∧
      (Q t).coeff m zw = eval (fun j => zw.2.val.rep j / zw.2.val.rep (c (1 : Fin 2))) A /
        eval (fun j => zw.2.val.rep j / zw.2.val.rep (c (1 : Fin 2))) B
    refine ⟨hden', ?_⟩
    change (map (parameterPullback F.Point) (P t)).coeff m zw = _
    rw [pullback_coeff, heval]
    exact heq
  · intro xy hxy
    obtain ⟨hn,heq⟩ := hrep xy hxy.1
    have hc : xy.1.val.rep (c (0 : Fin 2)) ≠ 0 := by
      simpa [M, MultiProjectiveSpace.coordinate, EmbeddedCommutativeGroup.additionPair,
        projectiveSquare] using hpivot xy hxy.2 (0 : Fin 2)
    obtain ⟨hn',hproj⟩ := projective_normalize
      (Pi.evalRingHom (fun _ : F.Point => K) xy.2) P 2 hP xy.1.val.rep (c (0 : Fin 2)) hc hn
    have hval : (fun t => eval₂ (Pi.evalRingHom (fun _ : F.Point × F.Point => K) xy)
        (fun j => xy.1.val.rep j / xy.1.val.rep (c (0 : Fin 2))) (Q t)) =
        (fun t => eval₂ (Pi.evalRingHom (fun _ : F.Point => K) xy.2)
          (fun j => xy.1.val.rep j / xy.1.val.rep (c (0 : Fin 2))) (P t)) := by
      funext t
      exact pullback_eval F.Point (P t) xy _
    change ∃ hout : (fun t => eval₂ (Pi.evalRingHom (fun _ : F.Point × F.Point => K) xy)
        (fun j => xy.1.val.rep j / xy.1.val.rep (c (0 : Fin 2))) (Q t)) ≠ 0,
      Projectivization.mk K _ hout = (xy.1 + xy.2).val
    rw [hval]
    exact ⟨hn', hproj.trans heq⟩

end PhilipponMultiplicity
end
end

set_option autoImplicit false
open PhilipponMultiplicity
open scoped BigOperators Topology

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ c : (projectiveSquare K F.ambientDimension).FactorIndex →
              Fin (F.ambientDimension+1),
          (∀ xy ∈ U, ∀ i : (projectiveSquare K F.ambientDimension).FactorIndex,
            (projectiveSquare K F.ambientDimension).coordinate
              (F.additionPair xy.1 xy.2) ⟨i,c i⟩ ≠ 0) ∧
          ∃ P : Fin (F.ambientDimension+1) →
              MvPolynomial (Fin (F.ambientDimension+1)) ((F.Point × F.Point) → K),
          (∀ t, ∀ m ∈ (P t).support, (∑ j, m j) ≤ 2) ∧
          (∀ t, ∀ m ∈ (P t).support, ∀ xy ∈ U,
            ∃ V : Set (F.Point × F.Point),
              @IsOpen _ (TopologicalSpace.induced (fun zw => F.additionPair zw.1 zw.2)
                (projectiveSquare K F.ambientDimension).zariskiTopology) V ∧ xy ∈ V ∧
              ∃ A B : MvPolynomial (Fin (F.ambientDimension+1)) K,
                ∀ zw ∈ U ∩ V,
                  let w : Fin (F.ambientDimension+1) → K := fun j =>
                    (projectiveSquare K F.ambientDimension).coordinate
                      (F.additionPair zw.1 zw.2) ⟨(1 : Fin 2),j⟩ /
                    (projectiveSquare K F.ambientDimension).coordinate
                      (F.additionPair zw.1 zw.2) ⟨(1 : Fin 2),c (1 : Fin 2)⟩
                  MvPolynomial.eval w B ≠ 0 ∧
                    (P t).coeff m zw = MvPolynomial.eval w A / MvPolynomial.eval w B) ∧
          ∀ xy ∈ U,
            let w : Fin (F.ambientDimension+1) → K := fun j =>
              (projectiveSquare K F.ambientDimension).coordinate
                (F.additionPair xy.1 xy.2) ⟨(0 : Fin 2),j⟩ /
              (projectiveSquare K F.ambientDimension).coordinate
                (F.additionPair xy.1 xy.2) ⟨(0 : Fin 2),c (0 : Fin 2)⟩
            ∃ h : (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point × F.Point => K) xy) w (P t)) ≠ 0,
              Projectivization.mk K (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point × F.Point => K) xy) w (P t)) h =
                  (xy.1+xy.2).val := by
  exact regular_coefficients_of_homogeneous_families K
    (exists_quadratic_homogeneous_translation_families K)

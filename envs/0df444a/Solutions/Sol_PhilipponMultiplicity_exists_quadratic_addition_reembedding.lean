-- Prove2me | solution 1 for PhilipponMultiplicity.exists_quadratic_addition_reembedding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T15:56:27.238602+00:00
-- url     : https://prove2.me/submissions/a597019b-32b8-486c-9a12-1b3af875442d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_quadratic_local_addition_reembedding
import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩


end MultiProjectiveSpace
end PhilipponMultiplicity
end
end

section
namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)


end PhilipponMultiplicity.MultiProjectiveSpace
end

section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]
theorem projectivization_mk_eq_iff_cross {ι : Type*}
    (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔
      ∀ j k, v j * w k = v k * w j := by
  classical
  constructor
  · intro heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp heq
    intro j k
    rw [← ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    change w k ≠ 0 at hk
    apply (Projectivization.mk_eq_mk_iff' K v w hv hw).mpr
    refine ⟨v k / w k, ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    exact h k j

/-- Regular maps into a multiprojective space have a closed equalizer, even
though the Zariski topology on the target is not Hausdorff. -/
theorem IsRegularAlong.isClosed_equalizer
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g) :
    @IsClosed X (TopologicalSpace.induced e M.zariskiTopology) {x | f x = g x} := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hx
  obtain ⟨U, hU, hxU, D, P, hP, hflift⟩ := hf x b
  obtain ⟨V, hV, hxV, E, Q, hQ, hglift⟩ := hg x b
  obtain ⟨hp, hpx⟩ := hflift x hxU
  obtain ⟨hq, hqx⟩ := hglift x hxV
  have hcross : ∃ j k, M.eval (P j * Q k - P k * Q j) (e x) ≠ 0 := by
    by_contra! hn
    apply hb
    rw [← hpx, ← hqx, projectivization_mk_eq_iff_cross]
    intro j k
    simpa only [eval, map_sub, map_mul, sub_eq_zero] using hn j k
  obtain ⟨j, k, hjk⟩ := hcross
  have hhom := ((hP j).mul M (hQ k)).sub M ((hP k).mul M (hQ j))
  let W := U ∩ V ∩ {p | M.eval (P j * Q k - P k * Q j) p ≠ 0}
  have hopen : IsOpen (e ⁻¹' W) :=
    ((hU.inter hV).inter (M.isOpen_basic _ _ hhom)).preimage continuous_induced_dom
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨hxU, hxV⟩, hjk⟩) ?_
  intro y hy heq
  obtain ⟨hpy, hpy'⟩ := hflift y hy.1.1
  obtain ⟨hqy, hqy'⟩ := hglift y hy.1.2
  have hmk := hpy'.trans ((congrFun heq b).trans hqy'.symm)
  have hz := (projectivization_mk_eq_iff_cross _ _ hpy hqy).mp hmk j k
  exact hy.2 (by simpa only [eval, map_sub, map_mul, sub_eq_zero] using hz)

theorem IsRegularAlong.eq_of_dense
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g)
    (A : Set X) (hA : @Dense X (TopologicalSpace.induced e M.zariskiTopology) A)
    (hfg : Set.EqOn f g A) : f = g := by
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  have hh : closure A ⊆ {x | f x = g x} :=
    closure_minimal hfg (hf.isClosed_equalizer M N hg)
  funext x
  exact hh (hA x)

theorem IsRegularAlong.comp_domain
    {X Y : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) (g : Y → X) :
    M.IsRegularAlong N (e ∘ g) (f ∘ g) := by
  intro y b
  obtain ⟨U, hU, hy, D, P, hP, hl⟩ := hf (g y) b
  exact ⟨U, hU, hy, D, P, hP, fun z hz => hl (g z) hz⟩


end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000
noncomputable section
open Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

namespace MultiProjectiveSpace

/-- The nonzero locus of a homogeneous coordinate tuple is open in the
actual induced polynomial Zariski topology. -/
theorem isOpen_tuple_nonzero {X : Type u} (M : MultiProjectiveSpace K)
    (e : X → M.Point) {n : ℕ} (D : M.FactorIndex → ℕ)
    (P : Fin (n+1) → M.CoordinateRing) (hP : ∀ j, M.IsHomogeneous (P j) D) :
    @IsOpen X (TopologicalSpace.induced e M.zariskiTopology)
      {x | (fun j => M.eval (P j) (e x)) ≠ 0} := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  have ho : IsOpen {y : X | M.eval (P j) (e y) ≠ 0} :=
    (M.isOpen_basic _ _ (hP j)).preimage continuous_induced_dom
  refine Filter.mem_of_superset (ho.mem_nhds hj) ?_
  intro y hy hz
  exact hy (congrFun hz j)

/-- A homogeneous tuple agreeing with a regular map on a nonempty open
piece of an irreducible domain agrees everywhere the tuple is nonzero.
No Hausdorff assumption on a Zariski space is used. -/
theorem IsRegularAlong.tuple_eq_of_nonempty_open
    {X : Type u} (M : MultiProjectiveSpace K) {n : ℕ}
    (e : X → M.Point) (f : X → (projectiveSpace K n).Point)
    (hf : M.IsRegularAlong (projectiveSpace K n) e f)
    (hirr : @IsPreirreducible X (TopologicalSpace.induced e M.zariskiTopology) univ)
    (U : Set X) (hU : @IsOpen X (TopologicalSpace.induced e M.zariskiTopology) U)
    (hne : U.Nonempty) (D : M.FactorIndex → ℕ)
    (P : Fin (n+1) → M.CoordinateRing) (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hlocal : ∀ x ∈ U, ∃ h : (fun j => M.eval (P j) (e x)) ≠ 0,
      Projectivization.mk K (fun j => M.eval (P j) (e x)) h = f x (0 : Fin 1)) :
    ∀ x (h : (fun j => M.eval (P j) (e x)) ≠ 0),
      Projectivization.mk K (fun j => M.eval (P j) (e x)) h = f x (0 : Fin 1) := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  let S : Set X := {x | (fun j => M.eval (P j) (e x)) ≠ 0}
  have hS : IsOpen S := M.isOpen_tuple_nonzero e D P hP
  let : PreirreducibleSpace S := Subtype.preirreducibleSpace
    (hirr.open_subset hS (subset_univ _))
  let q : S → (projectiveSpace K n).Point := fun x _ =>
    Projectivization.mk K (fun j => M.eval (P j) (e x.val)) x.property
  have hq : M.IsRegularAlong (projectiveSpace K n) (e ∘ Subtype.val) q := by
    intro x b
    exact ⟨univ, isOpen_univ, mem_univ _, D, P, hP,
      fun y _ => ⟨y.property, rfl⟩⟩
  have hopen : IsOpen (Subtype.val ⁻¹' U : Set S) := hU.preimage continuous_subtype_val
  have hnonempty : (Subtype.val ⁻¹' U : Set S).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, (hlocal x hx).choose⟩, hx⟩
  have hdense : @Dense S
      (TopologicalSpace.induced (e ∘ Subtype.val) M.zariskiTopology)
      (Subtype.val ⁻¹' U) := by
    rw [← induced_compose]
    exact hopen.dense hnonempty
  have heq := hq.eq_of_dense M (projectiveSpace K n) (hf.comp_domain Subtype.val)
    (Subtype.val ⁻¹' U) hdense (by
      intro x hx
      funext b
      have hb : b = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) b 0
      subst b
      exact (hlocal x.val hx).choose_spec)
  intro x hx
  exact congrFun (congrFun heq ⟨x, hx⟩) (0 : Fin 1)

end MultiProjectiveSpace

/-- The local addition tuple has unchanged bidegree when extended over its
entire nonzero locus. -/
def EmbeddedCommutativeGroup.additionLawOfLocal
    (F : EmbeddedCommutativeGroup K)
    (hirr : @IsPreirreducible (F.Point × F.Point)
      (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
        (projectiveSquare K F.ambientDimension).zariskiTopology) univ)
    (U : Set (F.Point × F.Point))
    (hU : @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
      (projectiveSquare K F.ambientDimension).zariskiTopology) U)
    (hne : U.Nonempty) (D : (projectiveSquare K F.ambientDimension).FactorIndex → ℕ)
    (P : Fin (F.ambientDimension+1) → (projectiveSquare K F.ambientDimension).CoordinateRing)
    (hP : ∀ j, (projectiveSquare K F.ambientDimension).IsHomogeneous (P j) D)
    (hlocal : ∀ xy ∈ U, ∃ h :
      (fun j => (projectiveSquare K F.ambientDimension).eval (P j)
        (F.additionPair xy.1 xy.2)) ≠ 0,
      Projectivization.mk K (fun j => (projectiveSquare K F.ambientDimension).eval
        (P j) (F.additionPair xy.1 xy.2)) h = (xy.1+xy.2).val) : F.AdditionLaw where
  degree := D
  coordinates := P
  homogeneous := hP
  represents := by
    intro x y h
    exact MultiProjectiveSpace.IsRegularAlong.tuple_eq_of_nonempty_open
      (X := F.Point × F.Point) (n := F.ambientDimension)
      (projectiveSquare K F.ambientDimension)
      (fun xy => F.additionPair xy.1 xy.2) (fun xy _ => (xy.1+xy.2).val)
      F.addition_regular hirr U hU hne D P hP hlocal (x,y) h

end PhilipponMultiplicity

end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology

namespace PhilipponMultiplicity

/-- Local quadratic formulas yield the globally compatible addition laws
required by the frontier theorem, without changing either degree. -/
theorem quadratic_addition_reembedding_of_local_formulas
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (hgeometry : ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        @IsPreirreducible (F.Point × F.Point)
          (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) Set.univ ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ D : (projectiveSquare K F.ambientDimension).FactorIndex → ℕ,
          ∃ P : Fin (F.ambientDimension+1) →
            (projectiveSquare K F.ambientDimension).CoordinateRing,
          D (0 : Fin 2) ≤ 2 ∧
          (∀ j, (projectiveSquare K F.ambientDimension).IsHomogeneous (P j) D) ∧
          ∀ xy ∈ U, ∃ h :
            (fun j => (projectiveSquare K F.ambientDimension).eval (P j)
              (F.additionPair xy.1 xy.2)) ≠ 0,
            Projectivization.mk K (fun j => (projectiveSquare K F.ambientDimension).eval
              (P j) (F.additionPair xy.1 xy.2)) h = (xy.1+xy.2).val)
    (E : EmbeddedCommutativeGroup K)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ) :
    ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
      ∀ x y : F.Point, ∃ law : F.AdditionLaw,
        law.degree (0 : Fin 2) ≤ 2 ∧
        (fun j => (projectiveSquare K F.ambientDimension).eval (law.coordinates j)
          (F.additionPair x y)) ≠ 0 := by
  obtain ⟨F, he, hirr, hcharts⟩ := hgeometry E hconnected
  refine ⟨F, he, ?_⟩
  intro x y
  obtain ⟨U, hU, hxy, D, P, hD, hP, hlocal⟩ := hcharts x y
  exact ⟨F.additionLawOfLocal hirr U hU ⟨(x,y),hxy⟩ D P hP hlocal,
    hD, (hlocal (x,y) hxy).choose⟩

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (E : EmbeddedCommutativeGroup K)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ) :
    ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
      ∀ x y : F.Point, ∃ law : F.AdditionLaw,
        law.degree (0 : Fin 2) ≤ 2 ∧
        (fun j => (projectiveSquare K F.ambientDimension).eval (law.coordinates j)
          (F.additionPair x y)) ≠ 0 := by
  exact quadratic_addition_reembedding_of_local_formulas K
    (exists_quadratic_local_addition_reembedding K) E hconnected

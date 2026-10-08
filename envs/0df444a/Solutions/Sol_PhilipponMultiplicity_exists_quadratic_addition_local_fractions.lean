-- Prove2me | solution 1 for PhilipponMultiplicity.exists_quadratic_addition_local_fractions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-05T19:11:56.362486+00:00
-- url     : https://prove2.me/submissions/f1950899-8741-440c-93f7-8c4132ee8a41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_quadratic_translation_regular_coefficients
import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support

set_option autoImplicit false

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.ParameterFractions
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Multiplication adds bounds on the degree in one chosen block. -/
theorem block_degree_le_mul (i : M.FactorIndex) (d e : ℕ)
    (P Q : M.CoordinateRing)
    (hP : ∀ a ∈ P.support, (∑ j, a ⟨i,j⟩) ≤ d)
    (hQ : ∀ a ∈ Q.support, (∑ j, a ⟨i,j⟩) ≤ e) :
    ∀ a ∈ (P * Q).support, (∑ j, a ⟨i,j⟩) ≤ d + e := by
  classical
  intro a ha
  obtain ⟨b,hb,c,hc,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q ha)
  simpa only [Finsupp.add_apply,Finset.sum_add_distrib] using
    Nat.add_le_add (hP b hb) (hQ c hc)

end ParameterFractions
end PhilipponMultiplicity
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.RegularCoefficients

variable {K : Type*} [Field K] (n : ℕ)

/-- Renaming a polynomial into the parameter block introduces no point degree. -/
theorem parameter_degree_zero (P : MvPolynomial (Fin (n+1)) K) :
    ∀ m ∈ (MvPolynomial.rename
      (fun j => (⟨(1 : Fin 2),j⟩ : ((_ : Fin 2) × Fin (n+1)))) P).support,
      (∑ j : Fin (n+1), m ⟨(0 : Fin 2),j⟩) = 0 := by
  classical
  intro m hm
  have hinj : Function.Injective
      (fun j : Fin (n+1) => (⟨(1 : Fin 2),j⟩ : ((_ : Fin 2) × Fin (n+1)))) := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  rw [MvPolynomial.support_rename_of_injective hinj] at hm
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  apply Finset.sum_eq_zero
  intro j _
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i,hi⟩
  have := congrArg Sigma.fst hi
  norm_num at this

/-- A monomial in the point block keeps its exact total degree. -/
theorem point_monomial_degree (a : Fin (n+1) →₀ ℕ) :
    ∀ m ∈ (MvPolynomial.rename
      (fun j => (⟨(0 : Fin 2),j⟩ : ((_ : Fin 2) × Fin (n+1))))
      (MvPolynomial.monomial a (1 : K))).support,
      (∑ j : Fin (n+1), m ⟨(0 : Fin 2),j⟩) = ∑ j, a j := by
  classical
  intro m hm
  have hinj : Function.Injective
      (fun j : Fin (n+1) => (⟨(0 : Fin 2),j⟩ : ((_ : Fin 2) × Fin (n+1)))) := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  rw [MvPolynomial.support_rename_of_injective hinj] at hm
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hm
  have hb' : a = b := by simpa using hb
  subst b
  simp only [Finsupp.mapDomain_apply hinj]

/-- Multiplying a point monomial by a parameter coefficient preserves the bound. -/
theorem term_degree_le (d : ℕ) (a : Fin (n+1) →₀ ℕ)
    (ha : (∑ j, a j) ≤ d) (P : MvPolynomial (Fin (n+1)) K) :
    ∀ m ∈ ((MvPolynomial.rename
      (fun j => (⟨(0 : Fin 2),j⟩ : ((_ : Fin 2) × Fin (n+1))))
      (MvPolynomial.monomial a (1 : K))) *
      MvPolynomial.rename
      (fun j => (⟨(1 : Fin 2),j⟩ : ((_ : Fin 2) × Fin (n+1)))) P).support,
      (∑ j : Fin (n+1), m ⟨(0 : Fin 2),j⟩) ≤ d := by
  simpa only [projectiveSquare,add_zero] using ParameterFractions.block_degree_le_mul
    (projectiveSquare K n) (0 : Fin 2) d 0 _ _
    (fun m hm => (point_monomial_degree n a m hm).trans_le ha)
    (fun m hm => (parameter_degree_zero n P m hm).le)

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

/-- Finitely many locally rational functions have simultaneous fractions on one
open neighborhood. The coordinates may be arbitrary functions on the space. -/
theorem simultaneous_fractions {σ : Type*} (a : X)
    (U : Set X) (hU : IsOpen U) (ha : a ∈ U)
    (v : X → σ → K) (f : ι → X → K)
    (hloc : ∀ t, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧
      ∃ A B : MvPolynomial σ K, ∀ x ∈ U ∩ V,
        MvPolynomial.eval (v x) B ≠ 0 ∧
        f t x = MvPolynomial.eval (v x) A / MvPolynomial.eval (v x) B) :
    ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∃ A B : ι → MvPolynomial σ K, ∀ x ∈ V, ∀ t,
        MvPolynomial.eval (v x) (B t) ≠ 0 ∧
        f t x = MvPolynomial.eval (v x) (A t) / MvPolynomial.eval (v x) (B t) := by
  classical
  choose V hV haV A B hAB using hloc
  refine ⟨U ∩ ⋂ t, V t, hU.inter (isOpen_iInter_of_finite hV),
    ⟨ha,Set.mem_iInter.mpr haV⟩, Set.inter_subset_left, A,B,?_⟩
  intro x hx t
  exact hAB t x ⟨hx.1,Set.mem_iInter.mp hx.2 t⟩

/-- Expanding a polynomial with locally rational coefficient functions gives
finite rational formulas whose point degree is bounded by the original degree. -/
theorem local_polynomial_fractions (d : ℕ) (a : X)
    (U : Set X) (hU : IsOpen U) (ha : a ∈ U)
    (v : X → ((_ : Fin 2) × Fin (n+1)) → K)
    (P : ι → MvPolynomial (Fin (n+1)) (X → K))
    (hdegree : ∀ t, ∀ m ∈ (P t).support, (∑ j, m j) ≤ d)
    (hloc : ∀ t, ∀ m ∈ (P t).support,
      ∃ V : Set X, IsOpen V ∧ a ∈ V ∧
        ∃ A B : MvPolynomial (Fin (n+1)) K, ∀ x ∈ U ∩ V,
          MvPolynomial.eval (fun j => v x ⟨(1 : Fin 2),j⟩) B ≠ 0 ∧
          (P t).coeff m x =
            MvPolynomial.eval (fun j => v x ⟨(1 : Fin 2),j⟩) A /
            MvPolynomial.eval (fun j => v x ⟨(1 : Fin 2),j⟩) B) :
    ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∃ (r : ℕ) (A B : ι → Fin r → MvPolynomial ((_ : Fin 2) × Fin (n+1)) K),
        (∀ t b, ∀ m ∈ (A t b).support, (∑ j, m ⟨(0 : Fin 2),j⟩) ≤ d) ∧
        (∀ t b, ∀ m ∈ (B t b).support, (∑ j, m ⟨(0 : Fin 2),j⟩) = 0) ∧
        ∀ x ∈ V, (∀ t b, MvPolynomial.eval (v x) (B t b) ≠ 0) ∧
          ∀ t, (∑ b, MvPolynomial.eval (v x) (A t b) /
            MvPolynomial.eval (v x) (B t b)) =
            MvPolynomial.eval₂ (Pi.evalRingHom (fun _ : X => K) x)
              (fun j => v x ⟨(0 : Fin 2),j⟩) (P t) := by
  classical
  let s := Finset.univ.biUnion (fun t => (P t).support)
  have hs (t : ι) : (P t).support ⊆ s := by
    intro m hm
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ t,hm⟩
  have hlocal : ∀ z : ι × s, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧
      ∃ A B : MvPolynomial (Fin (n+1)) K, ∀ x ∈ U ∩ V,
        MvPolynomial.eval (fun j => v x ⟨(1 : Fin 2),j⟩) B ≠ 0 ∧
        (P z.1).coeff z.2.val x =
          MvPolynomial.eval (fun j => v x ⟨(1 : Fin 2),j⟩) A /
          MvPolynomial.eval (fun j => v x ⟨(1 : Fin 2),j⟩) B := by
    intro z
    by_cases hm : z.2.val ∈ (P z.1).support
    · exact hloc z.1 z.2.val hm
    · refine ⟨Set.univ,isOpen_univ,Set.mem_univ a,0,1,?_⟩
      intro x _
      simp [MvPolynomial.notMem_support_iff.mp hm]
  obtain ⟨V,hV,haV,hVU,C,D,hCD⟩ := simultaneous_fractions a U hU ha
    (fun x j => v x ⟨(1 : Fin 2),j⟩)
    (fun z : ι × s => fun x => (P z.1).coeff z.2.val x) hlocal
  let e := (Fintype.equivFin s).symm
  let A (t : ι) (b : Fin (Fintype.card s)) : MvPolynomial ((_ : Fin 2) × Fin (n+1)) K :=
    MvPolynomial.rename (fun j => ⟨(0 : Fin 2),j⟩)
      (MvPolynomial.monomial (e b).val 1) *
    MvPolynomial.rename (fun j => ⟨(1 : Fin 2),j⟩) (C (t,e b))
  let B (t : ι) (b : Fin (Fintype.card s)) : MvPolynomial ((_ : Fin 2) × Fin (n+1)) K :=
    MvPolynomial.rename (fun j => ⟨(1 : Fin 2),j⟩) (D (t,e b))
  refine ⟨V,hV,haV,hVU,Fintype.card s,A,B,?_,?_,?_⟩
  · intro t b
    obtain ⟨u,_,hu⟩ := Finset.mem_biUnion.mp (e b).property
    exact term_degree_le n d (e b).val (hdegree u _ hu) (C (t,e b))
  · intro t b
    exact parameter_degree_zero n (D (t,e b))
  · intro x hx
    refine ⟨?_,?_⟩
    · intro t b
      simpa only [B,MvPolynomial.eval_rename,Function.comp_def] using (hCD x hx (t,e b)).1
    · intro t
      have hterm (b : Fin (Fintype.card s)) :
          MvPolynomial.eval (v x) (A t b) / MvPolynomial.eval (v x) (B t b) =
          (P t).coeff (e b).val x * ∏ j, v x ⟨(0 : Fin 2),j⟩ ^ (e b).val j := by
        rw [(hCD x hx (t,e b)).2]
        simp only [A,B,map_mul,MvPolynomial.eval_rename,Function.comp_def,
          MvPolynomial.eval_monomial,one_mul]
        rw [Finsupp.prod_pow]
        ring
      simp_rw [hterm]
      rw [e.sum_comp (fun m : s =>
        (P t).coeff m.val x * ∏ j, v x ⟨(0 : Fin 2),j⟩ ^ m.val j)]
      rw [MvPolynomial.eval₂_eq']
      change (∑ m : s, (P t).coeff m.val x * ∏ j, v x ⟨(0 : Fin 2),j⟩ ^ m.val j) = _
      rw [Finset.sum_coe_sort s (fun m =>
        (P t).coeff m x * ∏ j, v x ⟨(0 : Fin 2),j⟩ ^ m j)]
      symm
      apply Finset.sum_subset (hs t)
      intro m _ hm
      simp [MvPolynomial.notMem_support_iff.mp hm]

end PhilipponMultiplicity.RegularCoefficients
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

theorem quadratic_fractions_of_regular_coefficients
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (hgeometry : ∀ (E : EmbeddedCommutativeGroup K),
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
          ∃ (r : ℕ) (A B : Fin (F.ambientDimension+1) → Fin r →
              (projectiveSquare K F.ambientDimension).CoordinateRing),
          (∀ t a, ∀ m ∈ (A t a).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) ≤ 2) ∧
          (∀ t a, ∀ m ∈ (B t a).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) = 0) ∧
          ∀ xy ∈ U,
            let v : (projectiveSquare K F.ambientDimension).Variable → K :=
              fun w =>
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) w /
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
                  ⟨w.1,c w.1⟩
            (∀ t a, MvPolynomial.eval v (B t a) ≠ 0) ∧
            ∃ h : (fun t => ∑ a, MvPolynomial.eval v (A t a) /
                MvPolynomial.eval v (B t a)) ≠ 0,
              Projectivization.mk K (fun t => ∑ a, MvPolynomial.eval v (A t a) /
                MvPolynomial.eval v (B t a)) h = (xy.1+xy.2).val := by
  classical
  intro E hconnected
  obtain ⟨F,hF,hcharts⟩ := hgeometry E hconnected
  refine ⟨F,hF,?_⟩
  intro x y
  let : TopologicalSpace (F.Point × F.Point) :=
    TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
      (projectiveSquare K F.ambientDimension).zariskiTopology
  obtain ⟨U,hU,hxy,c,hc,P,hdegree,hregular,hrep⟩ := hcharts x y
  let v : (F.Point × F.Point) → (projectiveSquare K F.ambientDimension).Variable → K :=
    fun xy w =>
      (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) w /
      (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
        ⟨w.1,c w.1⟩
  obtain ⟨V,hV,hxyV,hVU,r,A,B,hA,hB,hvalues⟩ :=
    RegularCoefficients.local_polynomial_fractions F.ambientDimension 2 (x,y) U hU hxy v
      P hdegree (fun t m hm => hregular t m hm (x,y) hxy)
  refine ⟨V,hV,hxyV,c,(fun xy hxyV i => hc xy (hVU hxyV) i),r,A,B,hA,hB,?_⟩
  intro xy hxyV
  obtain ⟨hden,hval⟩ := hvalues xy hxyV
  obtain ⟨hne,heq⟩ := hrep xy (hVU hxyV)
  have hfun : (fun t => ∑ a, MvPolynomial.eval (v xy) (A t a) /
      MvPolynomial.eval (v xy) (B t a)) =
      (fun t => MvPolynomial.eval₂
        (Pi.evalRingHom (fun _ : F.Point × F.Point => K) xy)
        (fun j => v xy ⟨(0 : Fin 2),j⟩) (P t)) := funext hval
  refine ⟨hden,?_,?_⟩
  · rw [hfun]
    exact hne
  · apply Eq.trans ?_ heq
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ hne).mpr
    exact ⟨1, by simpa only [one_smul,v,projectiveSquare] using hfun.symm⟩

end PhilipponMultiplicity
end

end

set_option maxHeartbeats 1500000
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
          ∃ (r : ℕ) (A B : Fin (F.ambientDimension+1) → Fin r →
              (projectiveSquare K F.ambientDimension).CoordinateRing),
          (∀ t a, ∀ m ∈ (A t a).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) ≤ 2) ∧
          (∀ t a, ∀ m ∈ (B t a).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) = 0) ∧
          ∀ xy ∈ U,
            let v : (projectiveSquare K F.ambientDimension).Variable → K :=
              fun w =>
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) w /
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
                  ⟨w.1,c w.1⟩
            (∀ t a, MvPolynomial.eval v (B t a) ≠ 0) ∧
            ∃ h : (fun t => ∑ a, MvPolynomial.eval v (A t a) /
                MvPolynomial.eval v (B t a)) ≠ 0,
              Projectivization.mk K (fun t => ∑ a, MvPolynomial.eval v (A t a) /
                MvPolynomial.eval v (B t a)) h = (xy.1+xy.2).val := by
  exact quadratic_fractions_of_regular_coefficients K
    (exists_quadratic_translation_regular_coefficients K)

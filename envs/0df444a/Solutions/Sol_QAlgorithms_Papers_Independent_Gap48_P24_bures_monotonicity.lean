-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P24.bures_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:21:29.379579+00:00
-- url     : https://prove2.me/submissions/b3fc0d6b-81ab-4f57-a7e6-f416306f4a72

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24
noncomputable section

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq


theorem g74i_cp_idx {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (T : A →L[ℂ] B)
    (hT : IsCStarCompletelyPositive T) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι A) : ∃ Y : CStarMatrix ι ι B, (star X * X).map T = star Y * Y := by
  let e := Fintype.equivFin ι
  obtain ⟨Y0, h⟩ := hT _ (CStarMatrix.reindexₐ ℂ A e X)
  refine ⟨(CStarMatrix.reindexₐ ℂ B e).symm Y0, ?_⟩
  have h1 : star (CStarMatrix.reindexₐ ℂ A e X) * (CStarMatrix.reindexₐ ℂ A e X)
      = CStarMatrix.reindexₐ ℂ A e (star X * X) := by
    rw [map_mul, map_star]
  have h2 : star Y0 * Y0 = CStarMatrix.reindexₐ ℂ B e
      (star ((CStarMatrix.reindexₐ ℂ B e).symm Y0) * ((CStarMatrix.reindexₐ ℂ B e).symm Y0)) := by
    rw [map_mul, map_star, StarAlgEquiv.apply_symm_apply]
  rw [h1, h2] at h
  ext i j
  have := congrArg (fun M : CStarMatrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) B => M (e i) (e j)) h
  simp only [CStarMatrix.map_apply, CStarMatrix.reindexₐ_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply] at this
  rw [CStarMatrix.map_apply]
  have hr : ∀ (M : CStarMatrix ι ι B), (Matrix.reindex e e) M (e i) (e j) = M i j := fun M => by
    show M (e.symm (e i)) (e.symm (e j)) = M i j; simp
  have hr' : ∀ (M : CStarMatrix ι ι A), (Matrix.reindex e e) M (e i) (e j) = M i j := fun M => by
    show M (e.symm (e i)) (e.symm (e j)) = M i j; simp
  rw [hr, hr'] at this
  exact this

theorem g74i_sum_apply {B : Type v} [AddCommMonoid B] {κ ι : Type*} (s : Finset ι)
    (f : ι → CStarMatrix κ κ B) (a b : κ) : (∑ x ∈ s, f x) a b = ∑ x ∈ s, f x a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih]; rfl

theorem g74i_blk_mul {B : Type v} [NonUnitalCStarAlgebra B] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : CStarMatrix ι ι (CStarMatrix κ κ B)) (i j : ι) (a b : κ) :
    ((star Y * Y) i j) a b = ∑ k, ∑ c, star (Y k i c a) * Y k j c b := by
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply]
  rw [g74i_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [CStarMatrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [CStarMatrix.star_apply]

theorem g74i_flat_mul {B : Type v} [NonUnitalCStarAlgebra B] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : CStarMatrix ι ι (CStarMatrix κ κ B)) (Y' : CStarMatrix (ι × κ) (ι × κ) B)
    (hY : ∀ p q, Y' p q = Y p.1 q.1 p.2 q.2) (i j : ι) (a b : κ) :
    ((star Y * Y) i j) a b = (star Y' * Y') (i, a) (j, b) := by
  rw [g74i_blk_mul]
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, hY, Fintype.sum_prod_type]

def g74i_mapCLM {B : Type v} {D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
    {κ : Type*} (S : B →L[ℂ] D) : CStarMatrix κ κ B →L[ℂ] CStarMatrix κ κ D where
  toLinearMap := CStarMatrix.mapₗ S.toLinearMap
  cont := by
    show Continuous (fun M : Matrix κ κ B => fun i j => S (M i j))
    exact continuous_pi fun i => continuous_pi fun j =>
      S.continuous.comp ((continuous_apply j).comp (continuous_apply i))

theorem g74i_mapCLM_apply {B : Type v} {D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
    {κ : Type*} (S : B →L[ℂ] D) (M : CStarMatrix κ κ B) (i j : κ) :
    g74i_mapCLM S M i j = S (M i j) := rfl

theorem g74i_cp_comp_map {A : Type u} {B : Type v} {D : Type v} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (E : A →L[ℂ] CStarMatrix κ κ B) (hE : IsCStarCompletelyPositive E)
    (S : B →L[ℂ] D) (hS : IsCStarCompletelyPositive S) :
    IsCStarCompletelyPositive ((g74i_mapCLM S).comp E) := by
  intro n X
  obtain ⟨Y, hY⟩ := hE n X
  let Y' : CStarMatrix (Fin n × κ) (Fin n × κ) B := fun p q => Y p.1 q.1 p.2 q.2
  obtain ⟨Z', hZ⟩ := g74i_cp_idx S hS Y'
  let Z : CStarMatrix (Fin n) (Fin n) (CStarMatrix κ κ D) := fun i j a b => Z' (i, a) (j, b)
  refine ⟨Z, ?_⟩
  ext i j a b
  rw [g74i_flat_mul Z Z' (fun p q => rfl)]
  rw [← hZ]
  show S (E ((star X * X) i j) a b) = S ((star Y' * Y') (i, a) (j, b))
  rw [← g74i_flat_mul Y Y' (fun p q => rfl), ← hY]
  rfl

def g74i_f {B : Type v} [Add B] [Sub B] (M : CStarMatrix (Fin 2) (Fin 2) B) : B :=
  M 0 0 + M 1 1 - M 0 1 - M 1 0

theorem g74i_f_star_mul {B : Type v} [NonUnitalCStarAlgebra B] (y : CStarMatrix (Fin 2) (Fin 2) B) :
    g74i_f (star y * y) = ∑ k, star (y k 0 - y k 1) * (y k 0 - y k 1) := by
  simp only [g74i_f, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two, star_sub]
  noncomm_ring

theorem g74i_cp_one {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (T : A →L[ℂ] B)
    (hT : IsCStarCompletelyPositive T) (s : A) : ∃ y : B, T (star s * s) = star y * y := by
  let X : CStarMatrix (Fin 1) (Fin 1) A := fun _ _ => s
  obtain ⟨Y, hY⟩ := hT 1 X
  refine ⟨Y 0 0, ?_⟩
  have := congrArg (fun M : CStarMatrix (Fin 1) (Fin 1) B => M 0 0) hY
  have h0 : (star X * X) 0 0 = star s * s := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_one, CStarMatrix.star_apply]
  have h1 : (star Y * Y) 0 0 = star (Y 0 0) * Y 0 0 := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_one, CStarMatrix.star_apply]
  simp only [CStarMatrix.map_apply] at this
  rw [h0, h1] at this
  exact this

theorem g74i_f_E_nonneg {A : Type u} {B : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (E : A →L[ℂ] CStarMatrix (Fin 2) (Fin 2) B) (hE : IsCStarCompletelyPositive E)
    (c : A) (hc : 0 ≤ c) : 0 ≤ g74i_f (E c) := by
  rw [StarOrderedRing.nonneg_iff] at hc
  induction hc using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨y, hy⟩ := g74i_cp_one E hE s
    rw [hy, g74i_f_star_mul]
    exact Finset.sum_nonneg fun k _ => star_mul_self_nonneg _
  | zero => simp [g74i_f, CStarMatrix.zero_apply]
  | add x y _ _ hx hy =>
    have : g74i_f (E (x + y)) = g74i_f (E x) + g74i_f (E y) := by
      simp only [g74i_f, map_add, CStarMatrix.add_apply]; abel
    rw [this]; exact add_nonneg hx hy

theorem g74i_norm_one_le {D : Type*} [CStarAlgebra D] : ‖(1 : D)‖ ≤ 1 := by
  have h := CStarRing.norm_star_mul_self (x := (1 : D))
  simp only [star_one, mul_one] at h
  nlinarith [norm_nonneg (1 : D)]

theorem g74i_key {A : Type u} {B : Type v} {D : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (E : A →L[ℂ] CStarMatrix (Fin 2) (Fin 2) B) (hE : IsCStarCompletelyPositive E)
    (S : D →L[ℂ] A) (hS : IsCStarCompletelyPositive S) :
    ‖g74i_f (E (S 1))‖ ≤ ‖S‖ * ‖g74i_f (E 1)‖ := by
  obtain ⟨y, hy⟩ := g74i_cp_one S hS 1
  rw [star_one, one_mul] at hy
  have hc0 : 0 ≤ S 1 := by rw [hy]; exact star_mul_self_nonneg _
  have hsa : IsSelfAdjoint (S 1) := by rw [hy]; exact IsSelfAdjoint.star_mul_self _
  have hle := hsa.le_algebraMap_norm_self
  have hd : 0 ≤ algebraMap ℝ A ‖S 1‖ - S 1 := sub_nonneg.mpr hle
  have h1 := g74i_f_E_nonneg E hE _ hd
  have hlin : g74i_f (E (algebraMap ℝ A ‖S 1‖ - S 1)) =
      (‖S 1‖ : ℂ) • g74i_f (E 1) - g74i_f (E (S 1)) := by
    rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [g74i_f, map_sub, map_smul, CStarMatrix.sub_apply, CStarMatrix.smul_apply]
    module
  rw [hlin, sub_nonneg] at h1
  have h0 := g74i_f_E_nonneg E hE _ hc0
  have := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 h1
  rw [norm_smul] at this
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm] at this
  have hS1 : ‖S 1‖ ≤ ‖S‖ := by
    calc ‖S 1‖ ≤ ‖S‖ * ‖(1 : D)‖ := S.le_opNorm 1
      _ ≤ ‖S‖ * 1 := by gcongr; exact g74i_norm_one_le
      _ = ‖S‖ := mul_one _
  calc _ ≤ ‖S 1‖ * ‖g74i_f (E 1)‖ := this
    _ ≤ ‖S‖ * ‖g74i_f (E 1)‖ := by gcongr

theorem g74i_sInf_le (P Q : Set ℝ) (c : ℝ) (hc : 0 ≤ c) (hP : P.Nonempty) (hQ : ∀ q ∈ Q, 0 ≤ q)
    (h : ∀ r ∈ P, ∃ q ∈ Q, q ≤ c * r) : sInf Q ≤ c * sInf P := by
  rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg hc]
  apply le_csInf (hP.smul_set)
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨q, hq, hle⟩ := h r hr
  exact (csInf_le ⟨0, fun q hq => hQ q hq⟩ hq).trans hle

def g74i_diag {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (T1 T2 : A →L[ℂ] B) : A →L[ℂ] CStarMatrix (Fin 2) (Fin 2) B where
  toFun a := fun p q => if p = q then (if p = 0 then T1 a else T2 a) else 0
  map_add' x y := by
    refine CStarMatrix.ext fun p q => ?_
    show _ = (if p = q then (if p = 0 then T1 x else T2 x) else 0) +
      (if p = q then (if p = 0 then T1 y else T2 y) else 0)
    split_ifs <;> simp
  map_smul' c x := by
    refine CStarMatrix.ext fun p q => ?_
    show _ = c • (if p = q then (if p = 0 then T1 x else T2 x) else 0)
    split_ifs <;> simp
  cont := by
    show Continuous (fun a : A => ((fun p q => if p = q then (if p = 0 then T1 a else T2 a) else 0 :
      Matrix (Fin 2) (Fin 2) B)))
    refine continuous_pi fun p => continuous_pi fun q => ?_
    split_ifs
    exacts [T1.continuous, T2.continuous, continuous_const]

theorem g74i_diag_ext {A : Type u} {B : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (T1 T2 : A →L[ℂ] B) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2) :
    IsExtension T1 T2 (g74i_diag T1 T2) := by
  refine ⟨?_, fun a => ⟨rfl, rfl⟩⟩
  intro n X
  obtain ⟨Y1, hY1⟩ := h1 n X
  obtain ⟨Y2, hY2⟩ := h2 n X
  let Y : CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin 2) (Fin 2) B) :=
    fun k j p q => if p = q then (if p = 0 then Y1 k j else Y2 k j) else 0
  refine ⟨Y, ?_⟩
  ext i j p q
  rw [g74i_blk_mul]
  have e1 : T1 ((star X * X) i j) = ∑ k, star (Y1 k i) * Y1 k j := by
    have := congrArg (fun M : CStarMatrix (Fin n) (Fin n) B => M i j) hY1
    simp only [CStarMatrix.map_apply] at this
    rw [this, CStarMatrix.mul_apply]; simp only [CStarMatrix.star_apply]
  have e2 : T2 ((star X * X) i j) = ∑ k, star (Y2 k i) * Y2 k j := by
    have := congrArg (fun M : CStarMatrix (Fin n) (Fin n) B => M i j) hY2
    simp only [CStarMatrix.map_apply] at this
    rw [this, CStarMatrix.mul_apply]; simp only [CStarMatrix.star_apply]
  show (if p = q then (if p = 0 then T1 ((star X * X) i j) else T2 ((star X * X) i j)) else 0) = _
  rw [e1, e2]
  fin_cases p <;> fin_cases q <;> simp [Fin.sum_univ_two, Y]

/-- Proposition 8, PDF pp.12–13, (33)–(34): both composition directions, with
sqrt of the ordinary operator norm and independently quantified composing maps. -/
theorem solution {A B D : Type u}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (T1 T2 : A →L[ℂ] B) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2) :
    (∀ S : B →L[ℂ] D, IsCStarCompletelyPositive S →
      intrinsicBures (S.comp T1) (S.comp T2) ≤ Real.sqrt ‖S‖ * intrinsicBures T1 T2) ∧
    (∀ S : D →L[ℂ] A, IsCStarCompletelyPositive S →
      intrinsicBures (T1.comp S) (T2.comp S) ≤ Real.sqrt ‖S‖ * intrinsicBures T1 T2) := by
  have hne : Set.Nonempty {r : ℝ | ∃ E : A →L[ℂ] CStarMatrix (Fin 2) (Fin 2) B,
      IsExtension T1 T2 E ∧ r = extensionCost E} :=
    ⟨_, g74i_diag T1 T2, g74i_diag_ext T1 T2 h1 h2, rfl⟩
  constructor
  · intro S hS
    apply g74i_sInf_le _ _ _ (Real.sqrt_nonneg _) hne
    · rintro q ⟨E, _, rfl⟩; exact Real.sqrt_nonneg _
    · rintro r ⟨E, ⟨hE, hdiag⟩, rfl⟩
      refine ⟨_, ⟨(g74i_mapCLM S).comp E, ⟨g74i_cp_comp_map E hE S hS, fun a => ⟨?_, ?_⟩⟩, rfl⟩, ?_⟩
      · show S (E a 0 0) = S (T1 a); rw [(hdiag a).1]
      · show S (E a 1 1) = S (T2 a); rw [(hdiag a).2]
      · unfold extensionCost
        rw [← Real.sqrt_mul (norm_nonneg _)]
        apply Real.sqrt_le_sqrt
        have : ((g74i_mapCLM S).comp E) 1 0 0 + ((g74i_mapCLM S).comp E) 1 1 1
            - ((g74i_mapCLM S).comp E) 1 0 1 - ((g74i_mapCLM S).comp E) 1 1 0
            = S (E 1 0 0 + E 1 1 1 - E 1 0 1 - E 1 1 0) := by
          simp only [map_add, map_sub]; rfl
        rw [this]; exact S.le_opNorm _
  · intro S hS
    apply g74i_sInf_le _ _ _ (Real.sqrt_nonneg _) hne
    · rintro q ⟨E, _, rfl⟩; exact Real.sqrt_nonneg _
    · rintro r ⟨E, ⟨hE, hdiag⟩, rfl⟩
      refine ⟨_, ⟨E.comp S, ⟨?_, fun a => ⟨(hdiag (S a)).1, (hdiag (S a)).2⟩⟩, rfl⟩, ?_⟩
      · intro n X
        obtain ⟨Y, hY⟩ := hS n X
        obtain ⟨Z, hZ⟩ := hE n Y
        exact ⟨Z, by rw [← hZ, ← hY]; rfl⟩
      · show Real.sqrt ‖g74i_f (E (S 1))‖ ≤ Real.sqrt ‖S‖ * Real.sqrt ‖g74i_f (E 1)‖
        rw [← Real.sqrt_mul (norm_nonneg _)]
        exact Real.sqrt_le_sqrt (g74i_key E hE S hS)



end

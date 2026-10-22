-- Prove2me | solution 1 for RobinsonSR.Schur.lcp_unique_iff_pmatrix
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:37:32.021215+00:00
-- url     : https://prove2.me/submissions/a3a0aba1-ae81-4482-b98a-b41a97eed872

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting



namespace RobinsonSR.Schur

open scoped Matrix

def g_NSR {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → ∃ i, 0 < x i * (M *ᵥ x) i

def g_P {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (f : κ → ι), Function.Injective f →
    0 < (M.submatrix f f).det

lemma g_det_minor {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℝ) (k : κ) :
    (B.updateRow k (Pi.single k 1)).det =
      (B.submatrix (fun j : {j // j ≠ k} => (j : κ)) (fun j : {j // j ≠ k} => (j : κ))).det := by
  set C := B.updateRow k (Pi.single k 1)
  let e := Equiv.sumCompl (fun j : κ => j = k)
  rw [← Matrix.det_submatrix_equiv_self e C, ← Matrix.fromBlocks_toBlocks (C.submatrix e e)]
  have h12 : (C.submatrix e e).toBlocks₁₂ = 0 := by
    ext a b
    have ha : (a : κ) = k := a.2
    have hb : (b : κ) ≠ k := b.2
    simp [Matrix.toBlocks₁₂, C, e, ha, Pi.single_apply, hb]
  rw [h12, Matrix.det_fromBlocks_zero₁₂]
  have h11 : ((C.submatrix e e).toBlocks₁₁).det = 1 := by
    haveI : Unique {j : κ // j = k} := ⟨⟨⟨k, rfl⟩⟩, fun a => Subtype.ext a.2⟩
    rw [Matrix.det_unique]
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply]
    have hd : e (Sum.inl default) = k := (default : {j // j = k}).2
    rw [hd]
    simp [C]
  rw [h11, one_mul]
  congr 1
  ext a b
  have ha : (a : κ) ≠ k := a.2
  simp [Matrix.toBlocks₂₂, C, e, ha]

lemma g_det_update {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℝ) (k : κ) (c : ℝ) :
    (B + Matrix.diagonal (Pi.single k c)).det =
      B.det + c * (B.submatrix (fun j : {j // j ≠ k} => (j : κ)) (fun j : {j // j ≠ k} => (j : κ))).det := by
  have : B + Matrix.diagonal (Pi.single k c) = B.updateRow k (B k + c • Pi.single k 1) := by
    ext i j
    by_cases hi : i = k
    · subst hi; simp [Matrix.diagonal_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.diagonal_apply, Pi.single_apply, hi, Matrix.updateRow_ne hi]
  rw [this, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, g_det_minor]

lemma g_P_update {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : g_P A) (k : ι) (c : ℝ)
    (hc : 0 ≤ c) : g_P (A + Matrix.diagonal (Pi.single k c)) := by
  intro κ _ _ f hf
  have hsub : (A + Matrix.diagonal (Pi.single k c)).submatrix f f =
      A.submatrix f f + Matrix.diagonal (fun a => (Pi.single k c : ι → ℝ) (f a)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.diagonal_apply, hf.eq_iff]
  rw [hsub]
  by_cases hk : ∃ k', f k' = k
  · obtain ⟨k', rfl⟩ := hk
    have : (fun a => (Pi.single (f k') c : ι → ℝ) (f a)) = Pi.single k' c := by
      funext a
      by_cases ha : a = k'
      · subst ha; simp
      · simp [Pi.single_apply, hf.ne ha, ha]
    rw [this, g_det_update, Matrix.submatrix_submatrix]
    have h1 := hA κ f hf
    have h2 := hA {j // j ≠ k'} (f ∘ fun j => (j : κ)) (hf.comp Subtype.val_injective)
    positivity
  · push_neg at hk
    have : (fun a => (Pi.single k c : ι → ℝ) (f a)) = 0 := by
      funext a; simp [Pi.single_apply, hk a]
    rw [this]
    simpa using hA κ f hf

lemma g_P_diag {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : g_P A) (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) : g_P (A + Matrix.diagonal d) := by
  classical
  have key : ∀ S : Finset ι, g_P (A + Matrix.diagonal (fun i => if i ∈ S then d i else 0)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hA
    | insert k S hk ih =>
      have : (fun i => if i ∈ insert k S then d i else 0) =
          fun i => (if i ∈ S then d i else 0) + (Pi.single k (d k) : ι → ℝ) i := by
        funext i
        by_cases hi : i = k
        · subst hi; simp [hk]
        · simp [hi, Pi.single_apply]
      rw [this, ← Matrix.diagonal_add, ← add_assoc]
      exact g_P_update _ ih k _ (hd k)
  simpa using key Finset.univ

lemma g_P_sub {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι ι ℝ) (hA : g_P A)
    (f : κ → ι) (hf : Function.Injective f) : g_P (A.submatrix f f) := by
  intro κ' _ _ g hg
  rw [Matrix.submatrix_submatrix]
  exact hA _ (f ∘ g) (hf.comp hg)

lemma g_P_of_IsP {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : IsPMatrix A) :
    g_P A := by
  intro κ _ _ f hf
  by_cases hκ : IsEmpty κ
  · rw [Matrix.det_isEmpty]; exact one_pos
  · rw [not_isEmpty_iff] at hκ
    obtain ⟨a0⟩ := hκ
    set J : Finset ι := Finset.univ.map ⟨f, hf⟩
    have hmem : ∀ a, f a ∈ J := fun a => Finset.mem_map_of_mem _ (Finset.mem_univ a)
    let e : κ ≃ J := Equiv.ofBijective (fun a => ⟨f a, hmem a⟩) ⟨fun a b h => hf (by simpa using h),
      fun ⟨j, hj⟩ => by
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hj
        exact ⟨a, rfl⟩⟩
    have : A.submatrix f f = (A.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι))).submatrix e e := by
      ext a b; rfl
    rw [this, Matrix.det_submatrix_equiv_self]
    exact hA J ⟨f a0, hmem a0⟩

lemma g_NSR_of_P {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : g_P A) : g_NSR A := by
  intro x hx
  by_contra hcon
  push_neg at hcon
  let κ := {i // x i ≠ 0}
  let f : κ → ι := fun j => j
  have hf : Function.Injective f := Subtype.val_injective
  let d : κ → ℝ := fun j => -(A *ᵥ x) j / x j
  have hd : ∀ j, 0 ≤ d j := by
    intro j
    have h1 := hcon j
    have h2 : x j ≠ 0 := j.2
    have : d j = -(x j * (A *ᵥ x) j) / (x j) ^ 2 := by
      simp only [d]; field_simp
    rw [this]; apply div_nonneg _ (sq_nonneg _); linarith
  have hP := g_P_diag _ (g_P_sub A hA f hf) d hd
  have hdet := hP κ id Function.injective_id
  rw [Matrix.submatrix_id_id] at hdet
  have hsum : ∀ j : κ, (A.submatrix f f *ᵥ (fun i => x i)) j = (A *ᵥ x) j := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    have := Fintype.sum_subtype_add_sum_subtype (fun i => x i ≠ 0) (fun i => A j i * x i)
    rw [← this]
    have h0 : ∑ i : {i // ¬ x i ≠ 0}, A j i * x i = 0 := by
      apply Finset.sum_eq_zero; intro i _
      have : x i = 0 := by simpa using i.2
      simp [this]
    rw [h0, add_zero]
  have hzero : (A.submatrix f f + Matrix.diagonal d) *ᵥ (fun i => x i) = 0 := by
    funext j
    rw [Matrix.add_mulVec, Pi.add_apply, hsum, Matrix.mulVec_diagonal]
    have h2 : x j ≠ 0 := j.2
    simp only [d, Pi.zero_apply]
    field_simp
    ring
  have hne : (fun i : κ => x i) ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact hi (by simpa using congrFun h ⟨i, hi⟩)
  have : (A.submatrix f f + Matrix.diagonal d).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hzero⟩
  linarith


def g_hom {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  t • M + (1 - t) • (1 : Matrix ι ι ℝ)

lemma g_hom_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ) (i : ι) :
    (g_hom M t *ᵥ v) i = t * (M *ᵥ v) i + (1 - t) * v i := by
  simp [g_hom, Matrix.add_mulVec, Matrix.smul_mulVec]

lemma g_NSR_hom {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : g_NSR (g_hom M t) := by
  intro x hx
  obtain ⟨i, hi⟩ := hM x hx
  refine ⟨i, ?_⟩
  rw [g_hom_mulVec]
  have hxi : x i ≠ 0 := by
    intro h; rw [h] at hi; simp at hi
  have : 0 < x i ^ 2 := by positivity
  rcases eq_or_lt_of_le ht0 with h | h
  · subst h; nlinarith
  · nlinarith

lemma g_NSR_det_ne {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    M.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  obtain ⟨i, hi⟩ := hM v hv
  rw [hMv] at hi; simp at hi

lemma g_NSR_det_pos {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    0 < M.det := by
  let f : ℝ → ℝ := fun t => (g_hom M t).det
  have hf : Continuous f := by
    have : Continuous fun t : ℝ => g_hom M t := by
      unfold g_hom; fun_prop
    exact this.matrix_det
  have h0 : f 0 = 1 := by simp [f, g_hom]
  have h1 : f 1 = M.det := by simp [f, g_hom]
  by_contra hneg
  push_neg at hneg
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨by rw [h1]; exact hneg, by rw [h0]; exact zero_le_one⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' zero_le_one hf.continuousOn hmem
  exact g_NSR_det_ne _ (g_NSR_hom M hM t ht.1 ht.2) hft

lemma g_NSR_subfin {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M)
    (J : Finset ι) : g_NSR (M.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι))) := by
  intro x hx
  let y : ι → ℝ := fun i => if h : i ∈ J then x ⟨i, h⟩ else 0
  have hy : y ≠ 0 := by
    intro h
    apply hx; funext j
    have := congrFun h j
    simpa [y, j.2] using this
  obtain ⟨i, hi⟩ := hM y hy
  have hiJ : i ∈ J := by
    by_contra h; simp [y, h] at hi
  refine ⟨⟨i, hiJ⟩, ?_⟩
  have hsum : (M *ᵥ y) i = (M.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι)) *ᵥ x) ⟨i, hiJ⟩ := by
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [← Finset.sum_subset (Finset.subset_univ J)]
    · rw [← Finset.sum_coe_sort J]
      apply Finset.sum_congr rfl
      intro j _
      simp [y, j.2]
    · intro j _ hj
      simp [y, hj]
  have : y i = x ⟨i, hiJ⟩ := by simp [y, hiJ]
  rw [← this, ← hsum]; exact hi

lemma g_IsP_of_NSR {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    IsPMatrix M := fun J _ => g_NSR_det_pos _ (g_NSR_subfin M hM J)


def g_Sol {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (q w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∀ i, 0 ≤ (M *ᵥ w + q) i) ∧ (∀ i, w i * (M *ᵥ w + q) i = 0)

lemma g_dchoice (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = 0)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hab' : a' * b' = 0) :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ (1 - d) * (a - a') + d * (b - b') = 0 := by
  set α := a - a'
  set β := b - b'
  have hαβ : α * β ≤ 0 := by
    have : α * β = a * b - a * b' - a' * b + a' * b' := by ring
    rw [this, hab, hab']; nlinarith [mul_nonneg ha hb', mul_nonneg ha' hb]
  by_cases h : α - β = 0
  · have hα : α = β := by linarith
    have : α = 0 := by rw [← hα] at hαβ; nlinarith [sq_nonneg α]
    exact ⟨0, le_rfl, zero_le_one, by rw [this]; ring⟩
  · refine ⟨α / (α - β), ?_, ?_, ?_⟩
    · have : α / (α - β) = α * (α - β) / (α - β) ^ 2 := by field_simp
      rw [this]; apply div_nonneg _ (sq_nonneg _); nlinarith [sq_nonneg α]
    · have : 1 - α / (α - β) = -β * (α - β) / (α - β) ^ 2 := by field_simp; ring
      have h2 : 0 ≤ -β * (α - β) / (α - β) ^ 2 := by
        apply div_nonneg _ (sq_nonneg _); nlinarith [sq_nonneg β]
      linarith
    · field_simp; ring

lemma g_lcp_bound {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    ∃ c > 0, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ q q' w w' : ι → ℝ,
      g_Sol (g_hom M t) q w → g_Sol (g_hom M t) q' w' → c * ‖w - w'‖ ≤ ‖q - q'‖ := by
  let S : Set (ℝ × (ι → ℝ) × (ι → ℝ)) :=
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ι → ℝ) 1 ×ˢ Metric.sphere (0 : ι → ℝ) 1)
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod (isCompact_sphere _ _))
  let g : ℝ × (ι → ℝ) × (ι → ℝ) → ℝ := fun p =>
    ‖fun i => (1 - p.2.1 i) * p.2.2 i + p.2.1 i * (p.1 * (M *ᵥ p.2.2) i + (1 - p.1) * p.2.2 i)‖
  have hMc : Continuous fun x : ι → ℝ => M *ᵥ x :=
    (Matrix.mulVecLin M).continuous_of_finiteDimensional
  have hg : Continuous g := by
    have hc : ∀ i : ι, Continuous fun x : ι → ℝ => (M *ᵥ x) i := fun i =>
      (continuous_apply i).comp hMc
    apply continuous_norm.comp
    apply continuous_pi
    intro i
    have h1 : Continuous fun p : ℝ × (ι → ℝ) × (ι → ℝ) => (M *ᵥ p.2.2) i :=
      (hc i).comp (continuous_snd.comp continuous_snd)
    have h2 : Continuous fun p : ℝ × (ι → ℝ) × (ι → ℝ) => p.2.1 i :=
      (continuous_apply i).comp (continuous_fst.comp continuous_snd)
    have h3 : Continuous fun p : ℝ × (ι → ℝ) × (ι → ℝ) => p.2.2 i :=
      (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    have h4 : Continuous fun p : ℝ × (ι → ℝ) × (ι → ℝ) => p.1 := continuous_fst
    fun_prop
  have hpos : ∀ p ∈ S, 0 < g p := by
    rintro ⟨t, d, x⟩ ⟨ht, hd, hx⟩
    simp only [Metric.mem_sphere, dist_zero_right] at hx
    have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; exact zero_ne_one hx
    apply lt_of_le_of_ne (norm_nonneg _)
    intro h0
    have hz := norm_eq_zero.mp h0.symm
    obtain ⟨i, hi⟩ := g_NSR_hom M hM t ht.1 ht.2 x hx0
    rw [g_hom_mulVec] at hi
    have e := congrFun hz i
    simp only [Pi.zero_apply] at e
    have hdi0 : 0 ≤ d i := hd.1 i
    have hdi1 : d i ≤ 1 := hd.2 i
    set m := t * (M *ᵥ x) i + (1 - t) * x i
    -- (1 - d) x + d m = 0 ⇒ x m ≤ 0
    have : x i * m ≤ 0 := by
      rcases eq_or_lt_of_le hdi0 with h | h
      · rw [← h] at e; simp at e; rw [e]; simp
      · have hm : d i * (x i * m) = -(1 - d i) * x i ^ 2 := by
          have : d i * m = -((1 - d i) * x i) := by linarith
          calc d i * (x i * m) = x i * (d i * m) := by ring
            _ = _ := by rw [this]; ring
        have : d i * (x i * m) ≤ 0 := by rw [hm]; nlinarith [sq_nonneg (x i)]
        by_contra hc; push_neg at hc
        nlinarith
    linarith
  obtain ⟨c, hc, hcS⟩ : ∃ c > 0, ∀ p ∈ S, c ≤ g p := by
    by_cases hne : S.Nonempty
    · obtain ⟨p0, hp0, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
      exact ⟨g p0, hpos p0 hp0, fun p hp => hmin hp⟩
    · exact ⟨1, one_pos, fun p hp => absurd ⟨p, hp⟩ hne⟩
  refine ⟨c, hc, fun t ht0 ht1 q q' w w' hw hw' => ?_⟩
  by_cases hx : w - w' = 0
  · rw [hx, norm_zero, mul_zero]; exact norm_nonneg _
  have hxn : 0 < ‖w - w'‖ := norm_pos_iff.mpr hx
  have hd : ∀ i, ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ (1 - d) * (w i - w' i) +
      d * ((g_hom M t *ᵥ w + q) i - (g_hom M t *ᵥ w' + q') i) = 0 := fun i =>
    g_dchoice _ _ _ _ (hw.1 i) (hw.2.1 i) (hw.2.2 i) (hw'.1 i) (hw'.2.1 i) (hw'.2.2 i)
  choose d hd0 hd1 hdeq using hd
  set u := ‖w - w'‖⁻¹ • (w - w')
  have hu : (t, d, u) ∈ S := by
    refine ⟨⟨ht0, ht1⟩, ⟨fun i => hd0 i, fun i => hd1 i⟩, ?_⟩
    simp [u, norm_smul, hxn.ne']
  have hle := hcS _ hu
  have hgu : g (t, d, u) ≤ ‖w - w'‖⁻¹ * ‖q - q'‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have e := hdeq i
    have hlin : (g_hom M t *ᵥ w + q) i - (g_hom M t *ᵥ w' + q') i =
        t * (M *ᵥ (w - w')) i + (1 - t) * (w - w') i + (q - q') i := by
      simp only [Pi.add_apply, Pi.sub_apply, g_hom_mulVec, Matrix.mulVec_sub]; ring
    rw [hlin] at e
    have hcomp : (1 - d i) * u i + d i * (t * (M *ᵥ u) i + (1 - t) * u i) =
        ‖w - w'‖⁻¹ * (-(d i * (q - q') i)) := by
      simp only [u, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have : (1 - d i) * (w - w') i + d i * (t * (M *ᵥ (w - w')) i + (1 - t) * (w - w') i) =
          -(d i * (q - q') i) := by simp only [Pi.sub_apply] at e ⊢; linear_combination e
      rw [← this]; ring
    show ‖(1 - d i) * u i + d i * (t * (M *ᵥ u) i + (1 - t) * u i)‖ ≤ _
    rw [hcomp, norm_mul, norm_neg, norm_mul, Real.norm_eq_abs (‖w - w'‖⁻¹),
      abs_of_pos (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : ‖d i‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hd0 i, hd1 i]
    calc ‖d i‖ * ‖(q - q') i‖ ≤ 1 * ‖q - q'‖ :=
          mul_le_mul this (norm_le_pi_norm _ i) (norm_nonneg _) zero_le_one
      _ = ‖q - q'‖ := one_mul _
  have := hle.trans hgu
  have h2 : c * ‖w - w'‖ ≤ ‖w - w'‖⁻¹ * ‖q - q'‖ * ‖w - w'‖ :=
    mul_le_mul_of_nonneg_right this (norm_nonneg _)
  rwa [mul_assoc, mul_comm ‖q - q'‖, ← mul_assoc, inv_mul_cancel₀ hxn.ne', one_mul] at h2


lemma g_lcp_exists {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    ∀ q : ι → ℝ, ∃ w, g_Sol M q w := by
  obtain ⟨c, hc, hb⟩ := g_lcp_bound M hM
  let T := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (M - 1))
  have hT : ∀ v, ‖(M - 1) *ᵥ v‖ ≤ ‖T‖ * ‖v‖ := fun v => T.le_opNorm v
  set E := ‖T‖ + 1
  have hE : 0 < E := by positivity
  set δ := c / (2 * E)
  have hδ : 0 < δ := by positivity
  have key : ∀ k : ℕ, ∀ q, ∃ w, g_Sol (g_hom M (min (k * δ) 1)) q w := by
    intro k
    induction k with
    | zero =>
      intro q
      refine ⟨fun i => max (-q i) 0, ?_⟩
      have h1 : g_hom M (min ((0 : ℕ) * δ) 1) = 1 := by simp [g_hom]
      rw [h1]
      refine ⟨fun i => le_max_right _ _, fun i => ?_, fun i => ?_⟩
      · simp only [Matrix.one_mulVec, Pi.add_apply]
        rcases le_total 0 (q i) with h | h
        · rw [max_eq_right (by linarith)]; linarith
        · rw [max_eq_left (by linarith)]; linarith
      · simp only [Matrix.one_mulVec, Pi.add_apply]
        rcases le_total 0 (q i) with h | h
        · rw [max_eq_right (by linarith)]; ring
        · rw [max_eq_left (by linarith)]; ring
    | succ k ih =>
      intro q
      set t0 := min (k * δ) 1
      set t1 := min (((k + 1 : ℕ) : ℝ) * δ) 1
      have ht0 : 0 ≤ t0 := le_min (by positivity) zero_le_one
      have ht0' : t0 ≤ 1 := min_le_right _ _
      have hdt0 : 0 ≤ t1 - t0 := by
        have : t0 ≤ t1 := min_le_min_right _ (by push_cast; nlinarith)
        linarith
      have hdt1 : t1 - t0 ≤ δ := by
        have : t1 ≤ t0 + δ := by
          rcases le_total (k * δ) 1 with h | h
          · have : t0 = k * δ := min_eq_left h
            rw [this]; exact (min_le_left _ _).trans (by push_cast; linarith)
          · have : t0 = 1 := min_eq_right h
            rw [this]; exact (min_le_right _ _).trans (by linarith)
        linarith
      choose S hS using ih
      let Φ : (ι → ℝ) → (ι → ℝ) := fun w => S (q + (t1 - t0) • ((M - 1) *ᵥ w))
      have hlip : LipschitzWith (1 / 2 : NNReal) Φ := by
        apply LipschitzWith.of_dist_le_mul
        intro w w'
        rw [dist_eq_norm, dist_eq_norm]
        have h := hb t0 ht0 ht0' _ _ _ _ (hS (q + (t1 - t0) • ((M - 1) *ᵥ w)))
          (hS (q + (t1 - t0) • ((M - 1) *ᵥ w')))
        have he : q + (t1 - t0) • ((M - 1) *ᵥ w) - (q + (t1 - t0) • ((M - 1) *ᵥ w')) =
            (t1 - t0) • ((M - 1) *ᵥ (w - w')) := by
          rw [Matrix.mulVec_sub, smul_sub]; abel
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hdt0] at h
        have h2 := hT (w - w')
        have h3 : (t1 - t0) * ‖(M - 1) *ᵥ (w - w')‖ ≤ δ * (E * ‖w - w'‖) := by
          apply mul_le_mul hdt1 (h2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
            (norm_nonneg _) hδ.le
        have h4 : δ * (E * ‖w - w'‖) = c / 2 * ‖w - w'‖ := by
          simp only [δ]; field_simp
        have : c * ‖Φ w - Φ w'‖ ≤ c * (1 / 2 * ‖w - w'‖) := by
          simp only [Φ]; nlinarith
        have := le_of_mul_le_mul_left this hc
        simpa using this
      have hcon : ContractingWith (1 / 2 : NNReal) Φ := ⟨by
        rw [← NNReal.coe_lt_coe]; norm_num, hlip⟩
      set w := ContractingWith.fixedPoint Φ hcon
      have hw : Φ w = w := ContractingWith.fixedPoint_isFixedPt hcon
      refine ⟨w, ?_⟩
      have hsol := hS (q + (t1 - t0) • ((M - 1) *ᵥ w))
      change g_Sol _ _ (Φ w) at hsol
      rw [hw] at hsol
      have heq : g_hom M t0 *ᵥ w + (q + (t1 - t0) • ((M - 1) *ᵥ w)) = g_hom M t1 *ᵥ w + q := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, g_hom_mulVec, Matrix.sub_mulVec,
          Matrix.one_mulVec, Pi.sub_apply]
        ring
      rw [g_Sol, heq] at hsol
      exact hsol
  intro q
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / δ)
  have hk1 : 1 ≤ k * δ := by
    have := mul_le_mul_of_nonneg_right hk hδ.le
    rwa [div_mul_cancel₀ _ hδ.ne'] at this
  obtain ⟨w, hw⟩ := key k q
  rw [min_eq_right hk1] at hw
  refine ⟨w, ?_⟩
  have : g_hom M 1 = M := by simp [g_hom]
  rwa [this] at hw


lemma g_hom_one {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : g_hom M 1 = M := by
  simp [g_hom]

lemma g_lcp_unique {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M)
    (q w w' : ι → ℝ) (hw : g_Sol M q w) (hw' : g_Sol M q w') : w = w' := by
  obtain ⟨c, hc, hb⟩ := g_lcp_bound M hM
  rw [← g_hom_one M] at hw hw'
  have := hb 1 zero_le_one le_rfl q q w w' hw hw'
  rw [sub_self, norm_zero] at this
  have h0 : ‖w - w'‖ = 0 := by nlinarith [norm_nonneg (w - w')]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

lemma g_NSR_of_unique {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (h : ∀ q w w', g_Sol M q w → g_Sol M q w' → w = w') : g_NSR M := by
  intro x hx
  by_contra hcon
  push_neg at hcon
  let a : ι → ℝ := fun i => max (x i) 0
  let b : ι → ℝ := fun i => max (-x i) 0
  let p : ι → ℝ := fun i => max ((M *ᵥ x) i) 0
  have hx_ab : x = a - b := by
    funext i; simp only [a, b, Pi.sub_apply]
    rcases le_total 0 (x i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hMab : M *ᵥ a - M *ᵥ b = M *ᵥ x := by rw [← Matrix.mulVec_sub, ← hx_ab]
  have ha : g_Sol M (p - M *ᵥ a) a := by
    have e : M *ᵥ a + (p - M *ᵥ a) = p := by abel
    refine ⟨fun i => le_max_right _ _, fun i => ?_, fun i => ?_⟩
    · rw [e]; exact le_max_right _ _
    · rw [e]; simp only [a, p]
      rcases le_total (x i) 0 with h1 | h1
      · rw [max_eq_right h1]; ring
      · rcases eq_or_lt_of_le h1 with h2 | h2
        · rw [← h2]; simp
        · have : (M *ᵥ x) i ≤ 0 := by
            by_contra h3; push_neg at h3; nlinarith [hcon i]
          rw [max_eq_right this]; ring
  have hb : g_Sol M (p - M *ᵥ a) b := by
    have e : M *ᵥ b + (p - M *ᵥ a) = fun i => max (-(M *ᵥ x) i) 0 := by
      funext i
      have hi : (M *ᵥ x) i = (M *ᵥ a) i - (M *ᵥ b) i := by rw [← hMab]; rfl
      simp only [p, Pi.add_apply, Pi.sub_apply]
      rcases le_total 0 ((M *ᵥ x) i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; linarith
      · rw [max_eq_right h, max_eq_left (by linarith)]; linarith
    refine ⟨fun i => le_max_right _ _, fun i => ?_, fun i => ?_⟩
    · rw [e]; exact le_max_right _ _
    · rw [e]; simp only [b]
      rcases le_total 0 (x i) with h1 | h1
      · rw [max_eq_right (by linarith)]; ring
      · rcases eq_or_lt_of_le h1 with h2 | h2
        · rw [h2]; simp
        · have : 0 ≤ (M *ᵥ x) i := by
            by_contra h3; push_neg at h3; nlinarith [hcon i]
          rw [max_eq_right (by linarith : -(M *ᵥ x) i ≤ 0)]; ring
  have := h _ _ _ ha hb
  apply hx
  rw [hx_ab, this, sub_self]

lemma g_lcp_iff {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (z w : ι → ℝ) :
    ((∀ j, 0 ≤ (M *ᵥ w - z) j) ∧ (∀ j, 0 ≤ w j) ∧ w ⬝ᵥ (M *ᵥ w - z) = 0) ↔ g_Sol M (-z) w := by
  have e : M *ᵥ w + -z = M *ᵥ w - z := (sub_eq_add_neg _ _).symm
  unfold g_Sol
  rw [e]
  have hdot : ∀ (h1 : ∀ j, 0 ≤ (M *ᵥ w - z) j) (h2 : ∀ j, 0 ≤ w j),
      w ⬝ᵥ (M *ᵥ w - z) = 0 ↔ ∀ j, w j * (M *ᵥ w - z) j = 0 := by
    intro h1 h2
    unfold dotProduct
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (h2 j) (h1 j))]
    simp
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, (hdot h1 h2).mp h3⟩
  · rintro ⟨h2, h1, h3⟩
    exact ⟨h1, h2, (hdot h1 h2).mpr h3⟩

theorem lcp_core (s : ℕ) (M : Matrix (Fin s) (Fin s) ℝ) :
    (∀ z : Fin s → ℝ, ∃! w : Fin s → ℝ,
      (∀ j, 0 ≤ (M.mulVec w - z) j) ∧
      (∀ j, 0 ≤ w j) ∧
      w ⬝ᵥ (M.mulVec w - z) = 0) ↔ IsPMatrix M := by
  constructor
  · intro h
    apply g_IsP_of_NSR
    apply g_NSR_of_unique
    intro q w w' hw hw'
    obtain ⟨u, -, hu⟩ := h (-q)
    have e1 := hu w ((g_lcp_iff M (-q) w).mpr (by rwa [neg_neg]))
    have e2 := hu w' ((g_lcp_iff M (-q) w').mpr (by rwa [neg_neg]))
    rw [e1, e2]
  · intro hP z
    have hN := g_NSR_of_P M (g_P_of_IsP M hP)
    obtain ⟨w, hw⟩ := g_lcp_exists M hN (-z)
    refine ⟨w, (g_lcp_iff M z w).mpr hw, fun w' hw' => ?_⟩
    exact g_lcp_unique M hN (-z) w' w ((g_lcp_iff M z w').mp hw') hw

end RobinsonSR.Schur

open RobinsonSR.Schur


theorem solution (s : ℕ) (M : Matrix (Fin s) (Fin s) ℝ) :
    (∀ z : Fin s → ℝ, ∃! w : Fin s → ℝ,
      (∀ j, 0 ≤ (M.mulVec w - z) j) ∧
      (∀ j, 0 ≤ w j) ∧
      w ⬝ᵥ (M.mulVec w - z) = 0) ↔ IsPMatrix M := by
  exact lcp_core s M

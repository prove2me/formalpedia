-- Prove2me | solution 1 for SparseApprox.Greedy.norm_le_pinv_Z
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:26:30.7234+00:00
-- url     : https://prove2.me/submissions/89a6b1a6-da02-4af4-9da6-9720015445f9

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

lemma aux_npZ_normalize {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    normalizeVec v = 0 ∨ ‖normalizeVec v‖ = 1 := by
  by_cases hv : v = 0
  · left; simp [normalizeVec, hv]
  · right
    unfold normalizeVec
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

def aux_npZ_Inv {m n : ℕ} (a0 : Fin n → EuclideanSpace ℝ (Fin m)) (s : State m n) : Prop :=
  (∀ j ∈ s.chosen, s.col j ∈ Submodule.span ℝ (a0 '' ↑s.chosen)) ∧
  (∀ j ∉ s.chosen, s.col j ∈ (Submodule.span ℝ (a0 '' ↑s.chosen))ᗮ) ∧
  (∀ j ∉ s.chosen, s.col j ≠ 0 →
    ∃ c : ℝ, 1 ≤ c ∧ s.col j - c • a0 j ∈ Submodule.span ℝ (a0 '' ↑s.chosen)) ∧
  s.res ∈ (Submodule.span ℝ (a0 '' ↑s.chosen))ᗮ ∧
  (∀ j, s.col j = 0 ∨ ‖s.col j‖ = 1)

lemma aux_npZ_init {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    aux_npZ_Inv (initState A b).col (initState A b) := by
  have hc : (initState A b).chosen = ∅ := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simp [hc] at hj
  · intro j _
    rw [hc]; simp
  · intro j _ _
    refine ⟨1, le_refl _, ?_⟩
    simp
  · rw [hc]; simp
  · intro j
    exact aux_npZ_normalize _

lemma aux_npZ_orth {m : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (a ak z : EuclideanSpace ℝ (Fin m)) (c : ℝ) (hc : c ≠ 0) (hV : a - c • ak ∈ V)
    (hz : z ∈ Vᗮ) (haz : ⟪a, z⟫_ℝ = 0) :
    z ∈ (Submodule.span ℝ {ak} ⊔ V)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  obtain ⟨w, hw, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have h1 : ⟪v, z⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hv hz
  have h2 : ⟪a - c • ak, z⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hV hz
  rw [inner_sub_left, inner_smul_left, haz] at h2
  simp only [RCLike.conj_to_real] at h2
  have h3 : ⟪ak, z⟫_ℝ = 0 := by
    have : c * ⟪ak, z⟫_ℝ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc
    · exact h
  rw [inner_add_left, inner_smul_left, h3, h1]
  simp

lemma aux_npZ_step {m n : ℕ} (a0 : Fin n → EuclideanSpace ℝ (Fin m)) (s : State m n)
    (k : Fin n) (hk : k ∉ s.chosen) (hne : ⟪s.col k, s.res⟫_ℝ ≠ 0)
    (hs : aux_npZ_Inv a0 s) : aux_npZ_Inv a0 (greedyStep s k) := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := hs
  set V := Submodule.span ℝ (a0 '' ↑s.chosen) with hVdef
  set a := s.col k with hadef
  have ha0 : a ≠ 0 := by
    intro h; apply hne; rw [h, inner_zero_left]
  have ha1 : ‖a‖ = 1 := (hE k).resolve_left ha0
  have haa : ⟪a, a⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, ha1]; norm_num
  obtain ⟨ck, hck1, hckV⟩ := hC k hk ha0
  have hck0 : ck ≠ 0 := by linarith
  have hV' : Submodule.span ℝ (a0 '' ↑(insert k s.chosen)) = Submodule.span ℝ {a0 k} ⊔ V := by
    rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert]
  have hVle : V ≤ Submodule.span ℝ {a0 k} ⊔ V := le_sup_right
  have haV' : a ∈ Submodule.span ℝ {a0 k} ⊔ V := by
    have : a = ck • a0 k + (a - ck • a0 k) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _))) (hVle hckV)
  have horth : ∀ z, z ∈ Vᗮ → ⟪a, z⟫_ℝ = 0 → z ∈ (Submodule.span ℝ {a0 k} ⊔ V)ᗮ :=
    fun z hz haz => aux_npZ_orth V a (a0 k) z ck hck0 hckV hz haz
  have haV : a ∈ Vᗮ := hB k hk
  have hproj : ∀ x : EuclideanSpace ℝ (Fin m), x ∈ Vᗮ →
      x - ⟪a, x⟫_ℝ • a ∈ (Submodule.span ℝ {a0 k} ⊔ V)ᗮ := by
    intro x hx
    apply horth
    · exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ haV)
    · rw [inner_sub_right, inner_smul_right, haa]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [greedyStep] at hj ⊢
    rw [if_pos hj, hV']
    rcases Finset.mem_insert.mp hj with h | h
    · rw [h]; exact haV'
    · exact hVle (hA j h)
  · intro j hj
    simp only [greedyStep] at hj ⊢
    rw [if_neg hj, hV']
    have hjτ : j ∉ s.chosen := fun h => hj (Finset.mem_insert_of_mem h)
    unfold normalizeVec
    exact Submodule.smul_mem _ _ (hproj _ (hB j hjτ))
  · intro j hj hne'
    simp only [greedyStep] at hj hne' ⊢
    rw [if_neg hj] at hne' ⊢
    rw [hV']
    have hjτ : j ∉ s.chosen := fun h => hj (Finset.mem_insert_of_mem h)
    set x := s.col j - ⟪a, s.col j⟫_ℝ • a with hx
    have hx0 : x ≠ 0 := by
      intro h; apply hne'; rw [h]; simp [normalizeVec]
    have hcj : s.col j ≠ 0 := by
      intro h; apply hx0; rw [hx, h]; simp
    obtain ⟨c, hc1, hcV⟩ := hC j hjτ hcj
    have hcj1 : ‖s.col j‖ = 1 := (hE j).resolve_left hcj
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hxle : ‖x‖ ≤ 1 := by
      have e1 : ‖x‖ ^ 2 = ⟪x, s.col j⟫_ℝ := by
        rw [← real_inner_self_eq_norm_sq]
        conv_lhs => rw [hx]
        rw [inner_sub_right, inner_smul_right]
        have : ⟪x, a⟫_ℝ = 0 := by
          rw [hx, inner_sub_left, inner_smul_left, haa, real_inner_comm]
          simp
        rw [this]; ring
      have e2 : ⟪x, s.col j⟫_ℝ ≤ ‖x‖ * ‖s.col j‖ := real_inner_le_norm _ _
      rw [hcj1] at e2
      nlinarith
    refine ⟨‖x‖⁻¹ * c, ?_, ?_⟩
    · have : 1 ≤ ‖x‖⁻¹ := (one_le_inv₀ hxpos).mpr hxle
      nlinarith
    · have heq : normalizeVec x - (‖x‖⁻¹ * c) • a0 j =
          ‖x‖⁻¹ • ((s.col j - c • a0 j) - ⟪a, s.col j⟫_ℝ • a) := by
        unfold normalizeVec
        rw [mul_smul, ← smul_sub, hx]
        congr 1
        abel
      rw [heq]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hVle hcV) (Submodule.smul_mem _ _ haV'))
  · simp only [greedyStep]
    rw [hV']
    exact hproj _ hD
  · intro j
    simp only [greedyStep]
    split_ifs
    · exact hE j
    · exact aux_npZ_normalize _

lemma aux_npZ_inv_all {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (ε : ℝ) (k : ℕ → Fin n) (t : ℕ) (hrun : IsGreedyRun A b ε k t) :
    ∀ r, r ≤ t → aux_npZ_Inv (initState A b).col (greedyState A b k r) := by
  intro r
  induction r with
  | zero => intro _; exact aux_npZ_init A b
  | succ r ih =>
    intro h
    have hr : r < t := h
    exact aux_npZ_step _ _ (k r) (hrun r hr).2.1 (hrun r hr).2.2.1 (ih (le_of_lt hr))

theorem aux_npZ_core {m n : ℕ} (a0 : Fin n → EuclideanSpace ℝ (Fin m)) (st : State m n)
    (hinv : aux_npZ_Inv a0 st) (ε : ℝ) (hres : ε < ‖st.res‖) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol st.col st.res (ε / 2) u)
    (PZ : Matrix ↥(nzSet u ∪ st.chosen) (Fin m) ℝ)
    (hPZ : IsMoorePenrose (colsMatrix (fun i : ↥(nzSet u ∪ st.chosen) => a0 i)) PZ) :
    ‖u‖ ≤ 3 / 2 * opNorm2 PZ * ‖st.res‖ := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := hinv
  set V := Submodule.span ℝ (a0 '' ↑st.chosen) with hV
  have memN : ∀ i, i ∈ nzSet u ↔ u i ≠ 0 := by intro i; simp [nzSet]
  -- reduction principle
  have hred : ∀ v : EuclideanSpace ℝ (Fin n), ‖(∑ i, v i • st.col i) - st.res‖ ≤ ε / 2 →
      (∀ i, u i = 0 → v i = 0) → ∀ i0, u i0 ≠ 0 → v i0 = 0 → False := by
    intro v hv hsub i0 hu0 hv0
    have hcard := hu.2 v hv
    have hss : nzSet v ⊂ nzSet u := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨i0, by simp [nzSet, hu0], by simp [nzSet, hv0]⟩
      · intro i hi
        simp only [nzSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact fun h => hi (hsub i h)
    have := Finset.card_lt_card hss
    unfold nnz at hcard
    omega
  -- vanishing on st.chosen
  have hvan : ∀ i ∈ st.chosen, u i = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i0, hi0, hu0⟩ := hcon
    let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => if i ∈ st.chosen then 0 else u i)
    have hq : (∑ i, (if i ∈ st.chosen then u i else 0) • st.col i) ∈ V := by
      refine Submodule.sum_mem _ (fun i _ => ?_)
      by_cases hi : i ∈ st.chosen
      · rw [if_pos hi]; exact Submodule.smul_mem _ _ (hA i hi)
      · rw [if_neg hi, zero_smul]; exact Submodule.zero_mem _
    have hp : (∑ i, v i • st.col i) - st.res ∈ Vᗮ := by
      refine Submodule.sub_mem _ (Submodule.sum_mem _ (fun i _ => ?_)) hD
      by_cases hi : i ∈ st.chosen
      · simp [v, hi]
      · simp only [v, PiLp.toLp_apply, if_neg hi]; exact Submodule.smul_mem _ _ (hB i hi)
    have hdec : (∑ i, u i • st.col i) - st.res =
        (∑ i, (if i ∈ st.chosen then u i else 0) • st.col i) + ((∑ i, v i • st.col i) - st.res) := by
      have : ∀ i, u i • st.col i =
          (if i ∈ st.chosen then u i else 0) • st.col i + v i • st.col i := by
        intro i; by_cases hi : i ∈ st.chosen <;> simp [v, hi]
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]; abel
    have horth := Submodule.inner_right_of_mem_orthogonal hq hp
    have hvfeas : ‖(∑ i, v i • st.col i) - st.res‖ ≤ ε / 2 := by
      refine le_trans ?_ hu.1
      rw [hdec]
      have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      nlinarith [norm_nonneg (∑ i, (if i ∈ st.chosen then u i else 0) • st.col i),
        norm_nonneg ((∑ i, v i • st.col i) - st.res),
        norm_nonneg ((∑ i, (if i ∈ st.chosen then u i else 0) • st.col i) +
            ((∑ i, v i • st.col i) - st.res)),
        mul_self_nonneg ‖∑ i, (if i ∈ st.chosen then u i else 0) • st.col i‖]
    exact hred v hvfeas (fun i hi => by by_cases h : i ∈ st.chosen <;> simp [v, h, hi]) i0 hu0
      (by simp [v, hi0])
  -- kernel principle
  have hker : ∀ d : Fin n → ℝ, (∀ i, u i = 0 → d i = 0) → ∑ i, d i • st.col i = 0 →
      ∀ i, d i = 0 := by
    intro d hdsupp hdsum
    by_contra hcon
    push Not at hcon
    obtain ⟨i0, hd0⟩ := hcon
    have hu0 : u i0 ≠ 0 := fun h => hd0 (hdsupp i0 h)
    let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => u i - (u i0 / d i0) * d i)
    have hsum : ∑ i, v i • st.col i = ∑ i, u i • st.col i := by
      have : ∑ i, v i • st.col i =
          ∑ i, u i • st.col i - (u i0 / d i0) • ∑ i, d i • st.col i := by
        simp only [v, PiLp.toLp_apply, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum,
          smul_smul]
      rw [this, hdsum, smul_zero, sub_zero]
    refine hred v (by rw [hsum]; exact hu.1) (fun i hi => ?_) i0 hu0 ?_
    · simp [v, hi, hdsupp i hi]
    · simp only [v, PiLp.toLp_apply]
      rw [div_mul_cancel₀ _ hd0, sub_self]
  have hcol : ∀ i, u i ≠ 0 → st.col i ≠ 0 := by
    intro i hi h0
    have := hker (Pi.single i 1) (fun j hj => by
      by_cases hji : j = i
      · subst hji; exact absurd hj hi
      · simp [Pi.single_apply, hji]) (by simp [Pi.single_apply, h0]) i
    simp at this
  have hcex : ∀ i, ∃ c : ℝ, 1 ≤ c ∧ (u i ≠ 0 → st.col i - c • a0 i ∈ V) := by
    intro i
    by_cases hi : u i = 0
    · exact ⟨1, le_refl _, fun h => absurd hi h⟩
    · have hiτ : i ∉ st.chosen := fun h => hi (hvan i h)
      obtain ⟨c, hc1, hcV⟩ := hC i hiτ (hcol i hi)
      exact ⟨c, hc1, fun _ => hcV⟩
  choose cf hcf1 hcfV using hcex
  have hcf0 : ∀ i, cf i ≠ 0 := fun i => by linarith [hcf1 i]
  set Z := colsMatrix (fun i : ↥(nzSet u ∪ st.chosen) => a0 i) with hZ
  have hL : ∀ z : EuclideanSpace ℝ ↥(nzSet u ∪ st.chosen), Matrix.toEuclideanLin Z z = ∑ i : ↥(nzSet u ∪ st.chosen), z i • a0 i := by
    intro z; ext p
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, hZ, colsMatrix, mul_comm]
  have hrange : Submodule.span ℝ (a0 '' ↑(nzSet u ∪ st.chosen)) ≤ LinearMap.range (Matrix.toEuclideanLin Z) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨EuclideanSpace.single ⟨i, hi⟩ 1, ?_⟩
    rw [hL]
    simp [EuclideanSpace.single_apply]
  have hVS : V ≤ Submodule.span ℝ (a0 '' ↑(nzSet u ∪ st.chosen)) :=
    Submodule.span_mono (Set.image_mono (by simp))
  have hy_split : ∑ i, u i • st.col i =
      ∑ i, u i • (st.col i - cf i • a0 i) + ∑ i, (u i * cf i) • a0 i := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_sub, mul_smul]; abel
  have hyV1 : ∑ i, u i • (st.col i - cf i • a0 i) ∈ V := by
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : u i = 0
    · rw [hi, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (hcfV i hi)
  have hyS : ∑ i, u i • st.col i ∈ Submodule.span ℝ (a0 '' ↑(nzSet u ∪ st.chosen)) := by
    rw [hy_split]
    refine Submodule.add_mem _ (hVS hyV1) (Submodule.sum_mem _ (fun i _ => ?_))
    by_cases hi : u i = 0
    · rw [hi, zero_mul, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp [memN, hi], rfl⟩)
  obtain ⟨w, hw⟩ := hrange hyS
  have hZw' : Matrix.toEuclideanLin Z (Matrix.toEuclideanLin PZ (∑ i, u i • st.col i)) =
      ∑ i, u i • st.col i := by
    rw [← hw]
    rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
    simp only [WithLp.ofLp_toLp]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPZ.1]
  set w' := Matrix.toEuclideanLin PZ (∑ i, u i • st.col i) with hw'
  set W : Fin n → ℝ := fun i => if h : i ∈ (nzSet u ∪ st.chosen) then w' ⟨i, h⟩ else 0 with hW
  have hZW : Matrix.toEuclideanLin Z w' = ∑ i ∈ (nzSet u ∪ st.chosen), W i • a0 i := by
    rw [hL]
    refine Eq.trans ?_ (Finset.sum_coe_sort (nzSet u ∪ st.chosen) (fun i => W i • a0 i))
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hW, dif_pos i.2]
  have hdisj : Disjoint (nzSet u) st.chosen := by
    rw [Finset.disjoint_left]; intro i hiN hiτ; exact (memN i).mp hiN (hvan i hiτ)
  have hy2 : ∑ i, u i • st.col i = ∑ i ∈ (nzSet u), W i • a0 i + ∑ i ∈ st.chosen, W i • a0 i := by
    rw [← Finset.sum_union hdisj, ← hZW, hZw']
  have hsumN : ∑ i, (if u i = 0 then 0 else W i) • a0 i = ∑ i ∈ (nzSet u), W i • a0 i := by
    rw [nzSet, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : u i = 0 <;> simp [hi]
  set e : Fin n → ℝ := fun i => if u i = 0 then 0 else W i / cf i with he
  have hdsum_eq : ∑ i, (e i - u i) • st.col i =
      ∑ i, e i • (st.col i - cf i • a0 i) - ∑ i ∈ st.chosen, W i • a0 i := by
    have h1 : ∑ i, (e i - u i) • st.col i = ∑ i, e i • (st.col i - cf i • a0 i) +
        ∑ i, (if u i = 0 then 0 else W i) • a0 i - ∑ i, u i • st.col i := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : u i = 0
      · simp [he, hi]
      · simp only [he, if_neg hi, sub_smul, smul_sub, smul_smul]
        rw [div_mul_cancel₀ _ (hcf0 i)]; abel
    rw [h1, hsumN, hy2]; abel
  have hdV : ∑ i, (e i - u i) • st.col i ∈ V := by
    rw [hdsum_eq]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ (fun i _ => ?_))
      (Submodule.sum_mem _ (fun i hi => ?_))
    · by_cases hi : u i = 0
      · simp [he, hi]
      · exact Submodule.smul_mem _ _ (hcfV i hi)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hdVp : ∑ i, (e i - u i) • st.col i ∈ Vᗮ := by
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : u i = 0
    · simp [he, hi]
    · exact Submodule.smul_mem _ _ (hB i (fun h => hi (hvan i h)))
  have hd0 : ∑ i, (e i - u i) • st.col i = 0 := by
    have := Submodule.inner_right_of_mem_orthogonal hdV hdVp
    exact inner_self_eq_zero.mp this
  have hdz := hker (fun i => e i - u i) (fun i hi => by simp [he, hi]) hd0
  have hWu : ∀ i, u i ≠ 0 → W i = u i * cf i := by
    intro i hi
    have := hdz i
    simp only [he, if_neg hi] at this
    have h2 : W i / cf i = u i := by linarith
    rw [← h2, div_mul_cancel₀ _ (hcf0 i)]
  have hnorm_u : ‖u‖ ≤ ‖w'‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖u i‖ ^ 2 = ∑ i ∈ (nzSet u), ‖u i‖ ^ 2 := by
          symm; apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi; rw [memN] at hi; push Not at hi; simp [hi]
      _ ≤ ∑ i ∈ (nzSet u), ‖W i‖ ^ 2 := by
          apply Finset.sum_le_sum; intro i hi
          rw [memN] at hi
          rw [hWu i hi]
          simp only [Real.norm_eq_abs, sq_abs]
          have h1 : 1 ≤ cf i ^ 2 := by nlinarith [hcf1 i]
          have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (u i))
          nlinarith
      _ ≤ ∑ i ∈ (nzSet u ∪ st.chosen), ‖W i‖ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          intros; positivity
      _ = ∑ i : ↥(nzSet u ∪ st.chosen), ‖w' i‖ ^ 2 := by
          refine (Finset.sum_coe_sort (nzSet u ∪ st.chosen) (fun i => ‖W i‖ ^ 2)).symm.trans ?_
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hW, dif_pos i.2]
  have hw'le : ‖w'‖ ≤ opNorm2 PZ * ‖∑ i, u i • st.col i‖ := by
    have := ContinuousLinearMap.le_opNorm
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin PZ)) (∑ i, u i • st.col i)
    rw [LinearMap.coe_toContinuousLinearMap'] at this
    exact this
  have hbd : ‖∑ i, u i • st.col i‖ ≤ 3 / 2 * ‖st.res‖ := by
    calc ‖∑ i, u i • st.col i‖ = ‖(∑ i, u i • st.col i - st.res) + st.res‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖∑ i, u i • st.col i - st.res‖ + ‖st.res‖ := norm_add_le _ _
      _ ≤ ε / 2 + ‖st.res‖ := by linarith [hu.1]
      _ ≤ 3 / 2 * ‖st.res‖ := by linarith
  have hP0 : 0 ≤ opNorm2 PZ := norm_nonneg _
  calc ‖u‖ ≤ opNorm2 PZ * ‖∑ i, u i • st.col i‖ := le_trans hnorm_u hw'le
    _ ≤ opNorm2 PZ * (3 / 2 * ‖st.res‖) := mul_le_mul_of_nonneg_left hbd hP0
    _ = 3 / 2 * opNorm2 PZ * ‖st.res‖ := by ring

theorem aux_npZ_main {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (PZ : Matrix ↥(nzSet u ∪ (greedyState A b k r).chosen) (Fin m) ℝ)
    (hPZ : IsMoorePenrose
      (colsMatrix (fun i : ↥(nzSet u ∪ (greedyState A b k r).chosen) => (initState A b).col i))
      PZ) :
    ‖u‖ ≤ 3 / 2 * opNorm2 PZ * ‖(greedyState A b k r).res‖ :=
  aux_npZ_core (initState A b).col (greedyState A b k r)
    (aux_npZ_inv_all A b ε k t hrun r (le_of_lt hr)) ε (hrun r hr).1 u hu PZ hPZ

end SparseApprox.Greedy

open SparseApprox.Greedy
open scoped InnerProductSpace

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (PZ : Matrix ↥(nzSet u ∪ (greedyState A b k r).chosen) (Fin m) ℝ)
    (hPZ : IsMoorePenrose
      (colsMatrix (fun i : ↥(nzSet u ∪ (greedyState A b k r).chosen) => (initState A b).col i))
      PZ) :
    ‖u‖ ≤ 3 / 2 * opNorm2 PZ * ‖(greedyState A b k r).res‖ :=
  aux_npZ_main A b ε hε k t hrun r hr u hu PZ hPZ

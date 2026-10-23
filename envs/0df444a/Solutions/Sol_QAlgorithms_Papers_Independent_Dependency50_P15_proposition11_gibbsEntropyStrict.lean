-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P15.proposition11_gibbsEntropyStrict
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:45:49.726616+00:00
-- url     : https://prove2.me/submissions/17ff66f2-b1bc-45cc-9856-71ec1fa4be62

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

namespace X6P15s

open Real Filter Topology Set
open QAlgorithms.Papers.Independent.Dependency50.P15

lemma mul_exp_le (x b : ℝ) (hb : 0 < b) :
    x * exp (-b * x) ≤ (2 / b) * exp (-(b / 2) * x) := by
  have h1 : b / 2 * x ≤ exp (b / 2 * x) := by linarith [add_one_le_exp (b / 2 * x)]
  have hsplit : exp (-b * x) = exp (-(b / 2) * x) * exp (-(b / 2) * x) := by
    rw [← exp_add]; ring_nf
  rw [hsplit]
  have hx2 : x * exp (-(b / 2) * x) ≤ 2 / b := by
    rw [show -(b / 2) * x = -(b / 2 * x) by ring, exp_neg, ← div_eq_mul_inv,
      div_le_div_iff₀ (exp_pos _) hb]
    nlinarith
  calc x * (exp (-(b / 2) * x) * exp (-(b / 2) * x))
      = (x * exp (-(b / 2) * x)) * exp (-(b / 2) * x) := by ring
    _ ≤ _ := by gcongr

variable {I : Type*}

lemma summable_mul_exp (En : I → ℝ) (hE : ∀ i, 0 ≤ En i)
    (hs : ∀ b : ℝ, 0 < b → Summable (fun i => exp (-b * En i))) (b : ℝ) (hb : 0 < b) :
    Summable (fun i => En i * exp (-b * En i)) := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hE i) (exp_pos _).le)
    (fun i => mul_exp_le (En i) b hb) ((hs (b / 2) (by positivity)).mul_left _)

lemma negMulLog_le' (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p → 0 < q) :
    -(p * log p) ≤ q - p + -(p * log q) := by
  rcases hp.eq_or_lt with h | h
  · subst h; simp; exact hq
  · have hq' := hpq h
    have h1 := log_le_sub_one_of_pos (div_pos hq' h)
    rw [log_div hq'.ne' h.ne'] at h1
    have h2 : p * (log q - log p) ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left h1 h.le
    have h3 : p * (q / p - 1) = q - p := by field_simp
    nlinarith [h2, h3]

/-- Probability distributions on `I`. -/
structure IsDist (p : I → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  summ : Summable p
  one : ∑' i, p i = 1

lemma IsDist.le_one {p : I → ℝ} (hp : IsDist p) (i : I) : p i ≤ 1 := by
  rw [← hp.one]; exact hp.summ.le_tsum i (fun j _ => hp.nonneg j)

lemma negMulLog_nonneg' {p : I → ℝ} (hp : IsDist p) (i : I) : 0 ≤ -(p i * log (p i)) := by
  have := mul_nonpos_of_nonneg_of_nonpos (hp.nonneg i) (log_nonpos (hp.nonneg i) (hp.le_one i))
  linarith

lemma gibbs_cmp {p q : I → ℝ} (hp : IsDist p) (hq : IsDist q) (hpq : ∀ i, 0 < p i → 0 < q i)
    (hL : Summable fun i => -(p i * log (q i))) :
    Summable (fun i => -(p i * log (p i))) ∧
      ∑' i, -(p i * log (p i)) ≤ ∑' i, -(p i * log (q i)) := by
  have hR : Summable (fun i => q i - p i + -(p i * log (q i))) := (hq.summ.sub hp.summ).add hL
  have hle : ∀ i, -(p i * log (p i)) ≤ q i - p i + -(p i * log (q i)) := fun i =>
    negMulLog_le' (p i) (q i) (hp.nonneg i) (hq.nonneg i) (hpq i)
  have hS : Summable (fun i => -(p i * log (p i))) :=
    Summable.of_nonneg_of_le (negMulLog_nonneg' hp) hle hR
  refine ⟨hS, ?_⟩
  calc _ ≤ ∑' i, (q i - p i + -(p i * log (q i))) := Summable.tsum_le_tsum hle hS hR
    _ = _ := by
      rw [Summable.tsum_add (hq.summ.sub hp.summ) hL, Summable.tsum_sub hq.summ hp.summ,
        hp.one, hq.one]; ring

section Gibbs

variable (En : I → ℝ) (hG : IsGibbsSpectrum En)
include hG

lemma Z_ge_one (b : ℝ) (hb : 0 < b) : 1 ≤ partitionFunction En b := by
  obtain ⟨i0, hi0⟩ := hG.2.1
  have := (hG.2.2 b hb).le_tsum i0 (fun j _ => (exp_pos _).le)
  simpa [partitionFunction, hi0] using this

lemma finite_le (M : ℝ) : {i | En i ≤ M}.Finite := by
  by_contra hinf
  set Z1 := ∑' i, exp (-1 * En i)
  obtain ⟨K, hK⟩ := exists_nat_gt (Z1 * exp M)
  obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf K
  have h1 : ∑ i ∈ t, exp (-1 * En i) ≤ Z1 :=
    (hG.2.2 1 one_pos).sum_le_tsum t (fun j _ => (exp_pos _).le)
  have h2 : ∀ i ∈ t, exp (-M) ≤ exp (-1 * En i) := fun i hi =>
    exp_le_exp.2 (by have := ht hi; simp only [mem_setOf_eq] at this; linarith)
  have h3 : (K : ℝ) * exp (-M) ≤ Z1 := by
    calc (K : ℝ) * exp (-M) = ∑ i ∈ t, exp (-M) := by simp [htc]
      _ ≤ _ := Finset.sum_le_sum h2
      _ ≤ Z1 := h1
  have h4 : (K : ℝ) * exp (-M) * exp M = K := by rw [mul_assoc, ← exp_add]; simp
  have h5 : Z1 * exp M < K := hK
  nlinarith [exp_pos M, exp_pos (-M)]

omit hG in
lemma U_eq (b : ℝ) : thermalMeanEnergy En b =
    ∑' i, (exp (-b * En i) / partitionFunction En b) * En i := by
  unfold thermalMeanEnergy
  rw [← tsum_div_const]
  congr 1; ext i; ring

lemma U_cont (β : ℝ) (hβ : 0 < β) : ContinuousAt (thermalMeanEnergy En) β := by
  have hb : 0 < β / 2 := by positivity
  have hN : ContinuousOn (fun β => ∑' i, En i * exp (-β * En i)) (Ici (β / 2)) := by
    refine continuousOn_tsum (u := fun i => En i * exp (-(β / 2) * En i)) (fun i => by fun_prop)
      (summable_mul_exp En hG.1 hG.2.2 _ hb) ?_
    intro i x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hG.1 i) (exp_pos _).le)]
    apply mul_le_mul_of_nonneg_left _ (hG.1 i)
    apply exp_le_exp.2; have := hG.1 i; have : β / 2 ≤ x := hx; nlinarith
  have hZ : ContinuousOn (fun β => ∑' i, exp (-β * En i)) (Ici (β / 2)) := by
    refine continuousOn_tsum (u := fun i => exp (-(β / 2) * En i)) (fun i => by fun_prop)
      (hG.2.2 _ hb) ?_
    intro i x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le]
    apply exp_le_exp.2; have := hG.1 i; have : β / 2 ≤ x := hx; nlinarith
  have hmem : Ici (β / 2) ∈ 𝓝 β := Ici_mem_nhds (by linarith)
  have hZ1 := Z_ge_one En hG β hβ
  unfold thermalMeanEnergy partitionFunction
  exact (hN.continuousAt hmem).div (hZ.continuousAt hmem)
    (by unfold partitionFunction at hZ1; linarith)

lemma U_small (E : ℝ) (hE : 0 < E) : ∃ β, 0 < β ∧ thermalMeanEnergy En β ≤ E := by
  have ht : Tendsto (fun β : ℝ => ∑' i, En i * exp (-β * En i)) atTop
      (𝓝 (∑' _ : I, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun i => En i * exp (-1 * En i))
      (summable_mul_exp En hG.1 hG.2.2 1 one_pos) ?_ ?_
    · intro i
      rcases (hG.1 i).eq_or_lt with h | h
      · simp [← h]
      · have h1 : Tendsto (fun β : ℝ => -β * En i) atTop atBot :=
          tendsto_neg_atTop_atBot.atBot_mul_const h
        have : Tendsto (fun β : ℝ => exp (-β * En i)) atTop (𝓝 0) :=
          tendsto_exp_atBot.comp h1
        simpa using this.const_mul (En i)
    · filter_upwards [eventually_ge_atTop 1] with β hβ i
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hG.1 i) (exp_pos _).le)]
      apply mul_le_mul_of_nonneg_left _ (hG.1 i)
      apply exp_le_exp.2; have := hG.1 i; nlinarith
  rw [tsum_zero] at ht
  obtain ⟨β, hβ1, hβ2⟩ := ((ht.eventually (gt_mem_nhds hE)).and (eventually_gt_atTop 0)).exists
  refine ⟨β, hβ2, ?_⟩
  unfold thermalMeanEnergy
  have hZ1 := Z_ge_one En hG β hβ2
  rw [div_le_iff₀ (by linarith)]
  have hN0 : 0 ≤ ∑' i, En i * exp (-β * En i) :=
    tsum_nonneg fun i => mul_nonneg (hG.1 i) (exp_pos _).le
  nlinarith

lemma U_large [Infinite I] (E : ℝ) (hE : 0 < E) :
    ∃ δ, 0 < δ ∧ ∀ β, 0 < β → β < δ → E < thermalMeanEnergy En β := by
  classical
  set M := 2 * E + 2 with hM
  have hfin := finite_le En hG M
  set L := hfin.toFinset
  set n := L.card
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq I (2 * n + 2)
  have hg : Tendsto (fun β : ℝ => ∑ i ∈ F, exp (-β * En i)) (𝓝 0) (𝓝 (2 * n + 2 : ℝ)) := by
    have hc : Continuous (fun β : ℝ => ∑ i ∈ F, exp (-β * En i)) := by fun_prop
    have h0 : (fun β : ℝ => ∑ i ∈ F, exp (-β * En i)) 0 = 2 * n + 2 := by simp [hF]
    rw [← h0]; exact hc.tendsto 0
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1
    (hg.eventually (lt_mem_nhds (show (2 * n + 1 : ℝ) < 2 * n + 2 by linarith)))
  refine ⟨δ, hδ, fun β hβ hβδ => ?_⟩
  have hgβ : (2 * n + 1 : ℝ) < ∑ i ∈ F, exp (-β * En i) :=
    hδ' (by rw [Real.dist_eq, sub_zero, abs_of_pos hβ]; exact hβδ)
  set Z := partitionFunction En β with hZdef
  have hZF : ∑ i ∈ F, exp (-β * En i) ≤ Z :=
    (hG.2.2 β hβ).sum_le_tsum F (fun j _ => (exp_pos _).le)
  have hZgt : (2 * n + 1 : ℝ) < Z := lt_of_lt_of_le hgβ hZF
  have hZpos : 0 < Z := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set p : I → ℝ := fun i => exp (-β * En i) / Z with hp
  have hps : Summable p := (hG.2.2 β hβ).div_const Z
  have hpE : Summable (fun i => p i * En i) := by
    refine ((summable_mul_exp En hG.1 hG.2.2 β hβ).div_const Z).congr fun i => ?_
    simp only [hp]; ring
  have hp1 : ∑' i, p i = 1 := by
    simp only [hp]; rw [tsum_div_const]; exact div_self hZpos.ne'
  have hple : ∀ i, p i ≤ 1 / Z := by
    intro i; simp only [hp]
    apply div_le_div_of_nonneg_right _ hZpos.le
    rw [← exp_zero]; apply exp_le_exp.2; have := hG.1 i; nlinarith
  set f : I → ℝ := fun i => if i ∈ L then M * p i else 0 with hf
  have hfs : Summable f := summable_of_ne_finset_zero (s := L) (fun i hi => by simp [hf, hi])
  have hft : ∑' i, f i = ∑ i ∈ L, M * p i := by
    rw [tsum_eq_sum (s := L) (fun i hi => by simp [hf, hi])]
    exact Finset.sum_congr rfl fun i hi => by simp [hf, hi]
  have hpt : ∀ i, M * p i ≤ p i * En i + f i := by
    intro i
    have hp0 : 0 ≤ p i := div_nonneg (exp_pos _).le hZpos.le
    by_cases hi : i ∈ L
    · simp only [hf, if_pos hi]; nlinarith [hG.1 i]
    · simp only [hf, if_neg hi]
      have : M < En i := by
        by_contra h; push Not at h; exact hi (hfin.mem_toFinset.2 h)
      nlinarith
  have hsum : M ≤ ∑' i, p i * En i + ∑ i ∈ L, M * p i := by
    have := Summable.tsum_le_tsum hpt (hps.mul_left M) (hpE.add hfs)
    rw [tsum_mul_left, hp1, Summable.tsum_add hpE hfs, hft] at this
    linarith
  have hL : ∑ i ∈ L, M * p i ≤ M * n / Z := by
    calc ∑ i ∈ L, M * p i ≤ ∑ i ∈ L, M * (1 / Z) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hple i) (by positivity)
      _ = M * n / Z := by simp [n]; ring
  have hL2 : M * n / Z ≤ M / 2 := by
    rw [div_le_div_iff₀ hZpos (by norm_num)]
    have : (0 : ℝ) ≤ M := by positivity
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [U_eq En β]
  have : ∑' i, (exp (-β * En i) / partitionFunction En β) * En i = ∑' i, p i * En i := rfl
  rw [this]
  linarith

lemma beta_spec [Infinite I] (E : ℝ) (hE : 0 < E) :
    0 < gibbsInverseTemperature En E ∧
      thermalMeanEnergy En (gibbsInverseTemperature En E) = E := by
  set S := {β : ℝ | 0 < β ∧ thermalMeanEnergy En β ≤ E} with hS
  obtain ⟨β1, hβ1, hU1⟩ := U_small En hG E hE
  have hne : S.Nonempty := ⟨β1, hβ1, hU1⟩
  have hbdd : BddBelow S := ⟨0, fun β h => h.1.le⟩
  obtain ⟨δ, hδ, hδU⟩ := U_large En hG E hE
  have hge : δ ≤ sInf S := le_csInf hne (fun β hβ => by
    by_contra h; push Not at h; exact absurd hβ.2 (not_le.2 (hδU β hβ.1 h)))
  have hdef : gibbsInverseTemperature En E = sInf S := rfl
  rw [hdef]
  set b := sInf S with hbdef
  have hb : 0 < b := lt_of_lt_of_le hδ hge
  have hc := U_cont En hG b hb
  refine ⟨hb, le_antisymm ?_ ?_⟩
  · by_contra h; push Not at h
    have hev : ∀ᶠ β in 𝓝 b, E < thermalMeanEnergy En β := hc (Ioi_mem_nhds h)
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨β, hβS, hβlt⟩ := exists_lt_of_csInf_lt hne (show sInf S < b + ε by linarith)
    have hbβ : b ≤ β := csInf_le hbdd hβS
    have := hεb (show dist β b < ε by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    linarith [hβS.2]
  · by_contra h; push Not at h
    have hev : ∀ᶠ β in 𝓝 b, thermalMeanEnergy En β < E := hc (Iio_mem_nhds h)
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
    set β := max (b / 2) (b - ε / 2)
    have hβpos : 0 < β := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hβlt : β < b := max_lt (by linarith) (by linarith)
    have hβge : b - ε / 2 ≤ β := le_max_right _ _
    have hβS : β ∈ S := ⟨hβpos, (hεb (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)).le⟩
    have := csInf_le hbdd hβS
    linarith

end Gibbs

section Main

variable [Infinite I] (En : I → ℝ) (hG : IsGibbsSpectrum En)
include hG

lemma key (E : ℝ) (hE : 0 ≤ E) :
    IsDist (gibbsProbability En E) ∧ Summable (fun i => gibbsProbability En E i * En i) ∧
    ∑' i, gibbsProbability En E i * En i = E ∧
    ∀ p : I → ℝ, IsDist p → Summable (fun i => p i * En i) → ∑' i, p i * En i ≤ E →
      Summable (fun i => -(p i * log (p i))) ∧
      ∑' i, -(p i * log (p i)) ≤
        ∑' i, -(gibbsProbability En E i * log (gibbsProbability En E i)) := by
  classical
  rcases hE.eq_or_lt with h0 | hpos
  · subst h0
    have hfin := finite_le En hG 0
    set T := hfin.toFinset with hTdef
    have hT : ∀ i, i ∈ T ↔ En i = 0 := fun i => by
      rw [hfin.mem_toFinset]; simp only [mem_setOf_eq]
      exact ⟨fun h => le_antisymm h (hG.1 i), fun h => h.le⟩
    have hncard : (Set.ncard {j | En j = 0} : ℝ) = T.card := by
      have : {j | En j = 0} = {i | En i ≤ 0} := by
        ext i; simp only [mem_setOf_eq]; exact ⟨fun h => h.le, fun h => le_antisymm h (hG.1 i)⟩
      rw [this, Set.ncard_eq_toFinset_card _ hfin]
    obtain ⟨i0, hi0⟩ := hG.2.1
    have hcard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.2 ⟨i0, (hT i0).2 hi0⟩
    set c : ℝ := (T.card : ℝ) with hc
    have hq : ∀ i, gibbsProbability En 0 i = if i ∈ T then c⁻¹ else 0 := by
      intro i; unfold gibbsProbability; rw [if_pos rfl, hncard]
      by_cases h : En i = 0
      · rw [if_pos h, if_pos ((hT i).2 h)]
      · rw [if_neg h, if_neg (fun h' => h ((hT i).1 h'))]
    set q := gibbsProbability En 0 with hqdef
    have hqs : Summable q := summable_of_ne_finset_zero (s := T) (fun i hi => by rw [hq, if_neg hi])
    have hq1 : ∑' i, q i = 1 := by
      rw [tsum_eq_sum (s := T) (fun i hi => by rw [hq, if_neg hi]),
        Finset.sum_congr rfl (fun i hi => by rw [hq, if_pos hi])]
      rw [Finset.sum_const, nsmul_eq_mul, ← hc]; field_simp
    have hqd : IsDist q := ⟨fun i => by rw [hq]; split_ifs <;> positivity, hqs, hq1⟩
    have hqE0 : ∀ i, q i * En i = 0 := by
      intro i; rw [hq]; split_ifs with h
      · rw [(hT i).1 h, mul_zero]
      · rw [zero_mul]
    have hqlog : ∀ i, -(q i * log (q i)) = q i * log c := by
      intro i; rw [hq]; split_ifs
      · rw [log_inv]; ring
      · simp
    refine ⟨hqd, ?_, ?_, ?_⟩
    · simp only [hqE0]; exact summable_zero
    · simp only [hqE0, tsum_zero]
    · intro p hp hpE hmean
      have hpz : ∀ i, p i * En i = 0 := by
        intro i
        have h1 := hpE.le_tsum i (fun j _ => mul_nonneg (hp.nonneg j) (hG.1 j))
        have h2 := mul_nonneg (hp.nonneg i) (hG.1 i)
        linarith
      have hEz : ∀ i, 0 < p i → En i = 0 := by
        intro i hi
        rcases mul_eq_zero.1 (hpz i) with h | h
        · linarith
        · exact h
      have hpq : ∀ i, 0 < p i → 0 < q i := by
        intro i hi
        rw [hq, if_pos ((hT i).2 (hEz i hi))]; positivity
      have hpl : ∀ i, -(p i * log (q i)) = p i * log c := by
        intro i
        rcases (hp.nonneg i).eq_or_lt with h | h
        · rw [← h]; simp
        · rw [hq, if_pos ((hT i).2 (hEz i h)), log_inv]; ring
      have hL : Summable fun i => -(p i * log (q i)) := by
        simp only [hpl]; exact hp.summ.mul_right _
      obtain ⟨hS, hle⟩ := gibbs_cmp hp hqd hpq hL
      refine ⟨hS, hle.trans (le_of_eq ?_)⟩
      simp only [hpl, hqlog]; rw [tsum_mul_right, tsum_mul_right, hp.one, hq1]
  · obtain ⟨hb, hU⟩ := beta_spec En hG E hpos
    set b := gibbsInverseTemperature En E with hbdef
    set Z := partitionFunction En b with hZdef
    have hZ1 : 1 ≤ Z := Z_ge_one En hG b hb
    have hZpos : 0 < Z := by linarith
    have hq : ∀ i, gibbsProbability En E i = exp (-b * En i) / Z := by
      intro i; unfold gibbsProbability; rw [if_neg hpos.ne']
    set q := gibbsProbability En E with hqdef
    have hqs : Summable q := ((hG.2.2 b hb).div_const Z).congr (fun i => (hq i).symm)
    have hq1 : ∑' i, q i = 1 := by
      rw [tsum_congr hq, tsum_div_const]; exact div_self hZpos.ne'
    have hqd : IsDist q := ⟨fun i => by rw [hq]; positivity, hqs, hq1⟩
    have hqE : Summable (fun i => q i * En i) :=
      ((summable_mul_exp En hG.1 hG.2.2 b hb).div_const Z).congr (fun i => by rw [hq]; ring)
    have hmean : ∑' i, q i * En i = E := by
      rw [← hU, U_eq En b]; exact tsum_congr fun i => by rw [hq]
    have hlogq : ∀ i, log (q i) = -b * En i - log Z := by
      intro i; rw [hq, log_div (exp_pos _).ne' hZpos.ne', log_exp]
    refine ⟨hqd, hqE, hmean, ?_⟩
    intro p hp hpE hpm
    have hpl : ∀ i, -(p i * log (q i)) = b * (p i * En i) + log Z * p i := by
      intro i; rw [hlogq]; ring
    have hL : Summable fun i => -(p i * log (q i)) := by
      simp only [hpl]; exact (hpE.mul_left b).add (hp.summ.mul_left _)
    obtain ⟨hS, hle⟩ := gibbs_cmp hp hqd (fun i _ => by rw [hq]; positivity) hL
    refine ⟨hS, hle.trans ?_⟩
    have hql : ∀ i, -(q i * log (q i)) = b * (q i * En i) + log Z * q i := by
      intro i; rw [hlogq]; ring
    simp only [hpl, hql]
    rw [Summable.tsum_add (hpE.mul_left b) (hp.summ.mul_left _),
      Summable.tsum_add (hqE.mul_left b) (hqs.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_mul_left, tsum_mul_left, hp.one, hq1, hmean]
    nlinarith

lemma Hn_strictConcave : StrictConcaveOn ℝ (Ici 0)
    (fun E => ∑' i, -(gibbsProbability En E i * log (gibbsProbability En E i))) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hxy a b' ha hb hab
  simp only [smul_eq_mul]
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  obtain ⟨dx, sx, mx, maxx⟩ := key En hG x hx0
  obtain ⟨dy, sy, my, maxy⟩ := key En hG y hy0
  set qx := gibbsProbability En x with hqx
  set qy := gibbsProbability En y with hqy
  set m : I → ℝ := fun i => a * qx i + b' * qy i with hm
  have hmd : IsDist m := by
    refine ⟨fun i => add_nonneg (mul_nonneg ha.le (dx.nonneg i)) (mul_nonneg hb.le (dy.nonneg i)),
      (dx.summ.mul_left a).add (dy.summ.mul_left b'), ?_⟩
    rw [Summable.tsum_add (dx.summ.mul_left a) (dy.summ.mul_left b'), tsum_mul_left,
      tsum_mul_left, dx.one, dy.one]; linarith
  have hmE : Summable (fun i => m i * En i) :=
    ((sx.mul_left a).add (sy.mul_left b')).congr (fun i => by simp only [hm]; ring)
  have hmmean : ∑' i, m i * En i = a * x + b' * y := by
    rw [tsum_congr (fun i => show m i * En i = a * (qx i * En i) + b' * (qy i * En i) by
      simp only [hm]; ring), Summable.tsum_add (sx.mul_left a) (sy.mul_left b'),
      tsum_mul_left, tsum_mul_left, mx, my]
  have hz : 0 ≤ a * x + b' * y := by positivity
  obtain ⟨hmS, hmle⟩ := (key En hG _ hz).2.2.2 m hmd hmE hmmean.le
  obtain ⟨hxS, -⟩ := maxx qx dx sx mx.le
  obtain ⟨hyS, -⟩ := maxy qy dy sy my.le
  obtain ⟨i0, hi0⟩ : ∃ i, qx i ≠ qy i := by
    by_contra h; push Not at h
    have : qx = qy := funext h
    apply hxy; rw [← mx, ← my, this]
  have hterm : ∀ i, a * -(qx i * log (qx i)) + b' * -(qy i * log (qy i)) ≤
      -(m i * log (m i)) := by
    intro i
    have := strictConcaveOn_negMulLog.concaveOn.2 (show qx i ∈ Ici (0 : ℝ) from dx.nonneg i)
      (show qy i ∈ Ici (0 : ℝ) from dy.nonneg i) ha.le hb.le hab
    simp only [Real.negMulLog, smul_eq_mul] at this
    simp only [hm]; linarith
  have hterm0 : a * -(qx i0 * log (qx i0)) + b' * -(qy i0 * log (qy i0)) <
      -(m i0 * log (m i0)) := by
    have := strictConcaveOn_negMulLog.2 (show qx i0 ∈ Ici (0 : ℝ) from dx.nonneg i0)
      (show qy i0 ∈ Ici (0 : ℝ) from dy.nonneg i0) hi0 ha hb hab
    simp only [Real.negMulLog, smul_eq_mul] at this
    simp only [hm]; linarith
  calc a * (∑' i, -(qx i * log (qx i))) + b' * (∑' i, -(qy i * log (qy i)))
      = ∑' i, (a * -(qx i * log (qx i)) + b' * -(qy i * log (qy i))) := by
        rw [Summable.tsum_add (hxS.mul_left a) (hyS.mul_left b'), tsum_mul_left, tsum_mul_left]
    _ < ∑' i, -(m i * log (m i)) :=
        Summable.tsum_lt_tsum hterm hterm0 ((hxS.mul_left a).add (hyS.mul_left b')) hmS
    _ ≤ _ := hmle

end Main

end X6P15s

open QAlgorithms.Papers.Independent.Dependency50.P15 Real Set

theorem solution {I : Type*} [Countable I] [Infinite I]
    (energy : I → ℝ) (hGibbs : IsGibbsSpectrum energy) :
    StrictMonoOn (gibbsEntropy energy) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (gibbsEntropy energy) := by
  set Hn : ℝ → ℝ := fun E =>
    ∑' i, -(gibbsProbability energy E i * log (gibbsProbability energy E i)) with hHn
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hge : ∀ E, gibbsEntropy energy E = Hn E / log 2 := by
    intro E; unfold gibbsEntropy; rw [hHn, ← tsum_div_const]
    congr 1; ext i; rw [Real.logb]; ring
  have hSC := X6P15s.Hn_strictConcave energy hGibbs
  have hC : StrictConcaveOn ℝ (Ici 0) (gibbsEntropy energy) := by
    refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := hSC.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul, hge] at this ⊢
    rw [show a * (Hn x / log 2) + b * (Hn y / log 2) = (a * Hn x + b * Hn y) / log 2 by ring]
    exact div_lt_div_of_pos_right this hlog2
  refine ⟨?_, hC⟩
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hmono : gibbsEntropy energy ((x + y) / 2) ≤ gibbsEntropy energy y := by
    rw [hge, hge]
    apply div_le_div_of_nonneg_right _ hlog2.le
    obtain ⟨d, s, m, -⟩ := X6P15s.key energy hGibbs ((x + y) / 2) (by positivity)
    exact ((X6P15s.key energy hGibbs y hy0).2.2.2 _ d s (by rw [m]; linarith)).2
  have hc := hC.2 hx hy hxy.ne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [show 1 / 2 * x + 1 / 2 * y = (x + y) / 2 by ring] at hc
  linarith

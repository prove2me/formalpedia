-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P15.oscillator_gibbsUpperBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:37:17.044852+00:00
-- url     : https://prove2.me/submissions/ea48f4b5-3223-493d-8b4c-db12ec186fe0

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

namespace X6P15g

open Real Filter Topology Set

lemma mul_exp_le (x b : ℝ) (_hx : 0 ≤ x) (hb : 0 < b) :
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

/-- Summability of `E e^{-bE}`. -/
lemma summable_mul_exp (En : I → ℝ) (hE : ∀ i, 0 ≤ En i)
    (hs : ∀ b : ℝ, 0 < b → Summable (fun i => exp (-b * En i))) (b : ℝ) (hb : 0 < b) :
    Summable (fun i => En i * exp (-b * En i)) := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hE i) (exp_pos _).le)
    (fun i => mul_exp_le (En i) b (hE i) hb) ((hs (b / 2) (by positivity)).mul_left _)

lemma tsum_exp_pos (En : I → ℝ) (b : ℝ) (hs : Summable (fun i => exp (-b * En i)))
    (hne : Nonempty I) : 0 < ∑' i, exp (-b * En i) := by
  obtain ⟨i⟩ := hne
  exact hs.tsum_pos (fun j => (exp_pos _).le) i (exp_pos _)

/-- Gibbs variational inequality (in nats). -/
lemma gibbs_bound (En : I → ℝ) (hE : ∀ i, 0 ≤ En i)
    (hs : ∀ b : ℝ, 0 < b → Summable (fun i => exp (-b * En i)))
    (b b' : ℝ) (hb : 0 < b) (hb' : 0 < b') (hne : Nonempty I) :
    ∑' i, -((exp (-b * En i) / ∑' j, exp (-b * En j)) *
        log (exp (-b * En i) / ∑' j, exp (-b * En j))) ≤
      b' * ∑' i, (exp (-b * En i) / ∑' j, exp (-b * En j)) * En i +
        log (∑' j, exp (-b' * En j)) := by
  set Z := ∑' j, exp (-b * En j) with hZdef
  set Z' := ∑' j, exp (-b' * En j) with hZ'def
  have hZ : 0 < Z := tsum_exp_pos En b (hs b hb) hne
  have hZ' : 0 < Z' := tsum_exp_pos En b' (hs b' hb') hne
  set p : I → ℝ := fun i => exp (-b * En i) / Z with hp
  set q : I → ℝ := fun i => exp (-b' * En i) / Z' with hq
  have hp0 : ∀ i, 0 < p i := fun i => div_pos (exp_pos _) hZ
  have hq0 : ∀ i, 0 < q i := fun i => div_pos (exp_pos _) hZ'
  have hlogp : ∀ i, log (p i) = -b * En i - log Z := by
    intro i; simp only [hp]; rw [log_div (exp_pos _).ne' hZ.ne', log_exp]
  have hlogq : ∀ i, log (q i) = -b' * En i - log Z' := by
    intro i; simp only [hq]; rw [log_div (exp_pos _).ne' hZ'.ne', log_exp]
  have hps : Summable p := (hs b hb).div_const Z
  have hqs : Summable q := (hs b' hb').div_const Z'
  have hpE : Summable (fun i => p i * En i) := by
    have := (summable_mul_exp En hE hs b hb).div_const Z
    refine this.congr fun i => ?_
    simp only [hp]; ring
  have hsum1 : ∑' i, p i = 1 := by
    simp only [hp]; rw [tsum_div_const, div_self hZ.ne']
  have hsum1' : ∑' i, q i = 1 := by
    simp only [hq]; rw [tsum_div_const, div_self hZ'.ne']
  have hterm : ∀ i, -(p i * log (p i)) ≤
      (q i - p i) + b' * (p i * En i) + log Z' * p i := by
    intro i
    have h1 := log_le_sub_one_of_pos (div_pos (hq0 i) (hp0 i))
    rw [log_div (hq0 i).ne' (hp0 i).ne', hlogq] at h1
    have h2 : p i * (-b' * En i - log Z' - log (p i)) ≤ p i * (q i / p i - 1) :=
      mul_le_mul_of_nonneg_left h1 (hp0 i).le
    have h3 : p i * (q i / p i - 1) = q i - p i := by field_simp [(hp0 i).ne']
    nlinarith [h2, h3]
  have hL : Summable (fun i => -(p i * log (p i))) := by
    refine ((hpE.mul_left b).add (hps.mul_left (log Z))).congr fun i => ?_
    rw [hlogp]; ring
  have hR : Summable (fun i => (q i - p i) + b' * (p i * En i) + log Z' * p i) :=
    ((hqs.sub hps).add (hpE.mul_left b')).add (hps.mul_left _)
  calc ∑' i, -(p i * log (p i))
      ≤ ∑' i, ((q i - p i) + b' * (p i * En i) + log Z' * p i) :=
        Summable.tsum_le_tsum hterm hL hR
    _ = b' * ∑' i, p i * En i + log Z' := by
      rw [Summable.tsum_add ((hqs.sub hps).add (hpE.mul_left b')) (hps.mul_left _),
        Summable.tsum_add (hqs.sub hps) (hpE.mul_left b'), Summable.tsum_sub hqs hps,
        tsum_mul_left, tsum_mul_left, hsum1, hsum1']
      ring

/-- At the infimal inverse temperature the mean energy is at most `E`. -/
lemma mean_le (En : I → ℝ) (hE : ∀ i, 0 ≤ En i)
    (hs : ∀ b : ℝ, 0 < b → Summable (fun i => exp (-b * En i))) (hne : Nonempty I)
    (E : ℝ) (b : ℝ) (hb : 0 < b)
    (hbinf : b = sInf {β : ℝ | 0 < β ∧
      QAlgorithms.Papers.Independent.Dependency50.P15.thermalMeanEnergy En β ≤ E}) :
    ∑' i, (exp (-b * En i) / ∑' j, exp (-b * En j)) * En i ≤ E := by
  set S := {β : ℝ | 0 < β ∧
      QAlgorithms.Papers.Independent.Dependency50.P15.thermalMeanEnergy En β ≤ E}
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sInf_empty] at hbinf; linarith
  have hbdd : BddBelow S := ⟨0, fun β hβ => hβ.1.le⟩
  set Zf : ℝ → ℝ := fun β => ∑' j, exp (-β * En j) with hZf
  have hZc : ContinuousOn Zf (Ici b) := by
    refine continuousOn_tsum (u := fun j => exp (-b * En j)) (fun j => by fun_prop) (hs b hb) ?_
    intro j β hβ
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.2
    have := hE j
    have : b ≤ β := hβ
    nlinarith
  have hZpos : ∀ β, 0 < β → 0 < Zf β := fun β hβ => tsum_exp_pos En β (hs β hβ) hne
  have hpE : Summable (fun i => (exp (-b * En i) / Zf b) * En i) := by
    have := (summable_mul_exp En hE hs b hb).div_const (Zf b)
    refine this.congr fun i => ?_
    ring
  by_contra hgt
  push Not at hgt
  -- a finite partial sum already exceeds E
  obtain ⟨F, hF⟩ : ∃ F : Finset I, E < ∑ i ∈ F, (exp (-b * En i) / Zf b) * En i :=
    (hpE.hasSum.eventually (Ioi_mem_nhds hgt)).exists
  set g : ℝ → ℝ := fun β => ∑ i ∈ F, (exp (-β * En i) / Zf β) * En i
  have hgc : ContinuousWithinAt g (Ici b) b := by
    refine tendsto_finsetSum F fun i _ => ?_
    refine ContinuousWithinAt.mul ?_ continuousWithinAt_const
    refine ContinuousWithinAt.div (by fun_prop) (hZc b self_mem_Ici) (hZpos b hb).ne'
  have hev : ∀ᶠ β in 𝓝[≥] b, E < g β := hgc (Ioi_mem_nhds hF)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
  have hlt : sInf S < u := by rw [← hbinf]; exact hu
  obtain ⟨β, hβS, hβu⟩ := exists_lt_of_csInf_lt hSne hlt
  have hbβ : b ≤ β := by rw [hbinf]; exact csInf_le hbdd hβS
  have hgβ : E < g β := hsub ⟨hbβ, hβu⟩
  have hβ0 : 0 < β := hβS.1
  have hmean := hβS.2
  have hsβ : Summable (fun i => (exp (-β * En i) / Zf β) * En i) := by
    have := (summable_mul_exp En hE hs β hβ0).div_const (Zf β)
    refine this.congr fun i => ?_
    ring
  have : g β ≤ ∑' i, (exp (-β * En i) / Zf β) * En i :=
    hsβ.sum_le_tsum F (fun i _ => mul_nonneg (div_nonneg (exp_pos _).le (hZpos β hβ0).le) (hE i))
  have heq : ∑' i, (exp (-β * En i) / Zf β) * En i =
      QAlgorithms.Papers.Independent.Dependency50.P15.thermalMeanEnergy En β := by
    unfold QAlgorithms.Papers.Independent.Dependency50.P15.thermalMeanEnergy
      QAlgorithms.Papers.Independent.Dependency50.P15.partitionFunction
    rw [← tsum_div_const]
    congr 1; ext i; simp only [hZf]; ring
  linarith

open QAlgorithms.Papers.Independent.Dependency50.P15 in
lemma osc_exp {ell : ℕ} (a : Fin ell → ℝ) (β : ℝ) (n : Fin ell → ℕ) :
    exp (-β * oscillatorEnergy a n) = ∏ i, exp (-β * a i) ^ n i := by
  unfold oscillatorEnergy
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.exp_nat_mul]; ring_nf

lemma geom_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, r ^ k ≤ (1 - r)⁻¹ := by
  rw [geom_sum_eq h1.ne, show (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) by
    rw [← neg_div_neg_eq]; ring_nf, inv_eq_one_div]
  have : 0 ≤ r ^ N := pow_nonneg h0 N
  gcongr
  linarith

open QAlgorithms.Papers.Independent.Dependency50.P15 in
lemma box {ell : ℕ} (a : Fin ell → ℝ) (ha : ∀ i, 0 < a i) (β : ℝ) (hβ : 0 < β)
    (F : Finset (Fin ell → ℕ)) :
    ∑ n ∈ F, exp (-β * oscillatorEnergy a n) ≤ ∏ i, (1 - exp (-β * a i))⁻¹ := by
  classical
  set N := F.sup (fun n => Finset.univ.sup n)
  have hsub : F ⊆ Fintype.piFinset (fun _ => Finset.range (N + 1)) := by
    intro n hn; rw [Fintype.mem_piFinset]; intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.le_sup (f := n) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun n => Finset.univ.sup n) hn)
  calc ∑ n ∈ F, exp (-β * oscillatorEnergy a n)
      ≤ ∑ n ∈ Fintype.piFinset (fun _ => Finset.range (N + 1)),
          exp (-β * oscillatorEnergy a n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (exp_pos _).le)
    _ = ∏ i, ∑ k ∈ Finset.range (N + 1), exp (-β * a i) ^ k := by
        rw [Finset.prod_univ_sum]; exact Finset.sum_congr rfl fun n _ => osc_exp a β n
    _ ≤ _ := Finset.prod_le_prod
        (fun i _ => Finset.sum_nonneg fun _ _ => pow_nonneg (exp_pos _).le _)
        (fun i _ => geom_le _ (exp_pos _).le (by
          have := ha i
          calc exp (-β * a i) < exp 0 := exp_lt_exp.2 (by nlinarith)
            _ = 1 := exp_zero) _)

lemma inv_bound (x : ℝ) (hx : 0 < x) : (1 - exp (-x))⁻¹ ≤ 1 + 1 / x := by
  have h1 : 1 + x ≤ exp x := by linarith [add_one_le_exp x]
  have h2 : exp (-x) ≤ 1 / (1 + x) := by
    rw [exp_neg, ← one_div]; exact one_div_le_one_div_of_le (by linarith) h1
  have h3 : x / (1 + x) ≤ 1 - exp (-x) := by
    have : 1 / (1 + x) = 1 - x / (1 + x) := by field_simp; ring
    linarith
  have h4 : 0 < x / (1 + x) := by positivity
  calc (1 - exp (-x))⁻¹ ≤ (x / (1 + x))⁻¹ := inv_anti₀ h4 h3
    _ = 1 + 1 / x := by field_simp; ring

end X6P15g

open QAlgorithms.Papers.Independent.Dependency50.P15 Real

theorem solution (ell : ℕ) (hell : 1 ≤ ell)
    (a : Fin ell → ℝ) (ha : ∀ i, 0 < a i) (E : ℝ) (hE : 0 ≤ E) :
    gibbsEntropy (oscillatorEnergy a) E ≤
      (ell : ℝ) * Real.logb 2 (Real.exp 1) +
        ∑ i, Real.logb 2 (1 + E / ((ell : ℝ) * a i)) := by
  classical
  set En := oscillatorEnergy a with hEndef
  have hEn : ∀ n, 0 ≤ En n := fun n =>
    Finset.sum_nonneg fun i _ => mul_nonneg (ha i).le (Nat.cast_nonneg _)
  have hs : ∀ b : ℝ, 0 < b → Summable (fun n => exp (-b * En n)) := fun b hb =>
    summable_of_sum_le (fun n => (exp_pos _).le) (X6P15g.box a ha b hb)
  have hell0 : (0 : ℝ) < ell := by exact_mod_cast hell
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hRHS0 : 0 ≤ (ell : ℝ) * Real.logb 2 (Real.exp 1) +
      ∑ i, Real.logb 2 (1 + E / ((ell : ℝ) * a i)) := by
    apply add_nonneg
    · apply mul_nonneg hell0.le
      rw [Real.logb, log_exp]; exact div_nonneg zero_le_one hlog2.le
    · apply Finset.sum_nonneg; intro i _
      apply Real.logb_nonneg (by norm_num)
      have : 0 ≤ E / (ell * a i) := div_nonneg hE (mul_nonneg hell0.le (ha i).le)
      linarith
  have hne : Nonempty (Fin ell → ℕ) := ⟨0⟩
  have hinf : Infinite (Fin ell → ℕ) :=
    Infinite.of_injective (fun k : ℕ => fun _ : Fin ell => k)
      (by intro x y h; exact congrFun h ⟨0, hell⟩)
  rcases hE.eq_or_lt with hE0 | hEpos
  · subst hE0
    have hground : {j : Fin ell → ℕ | En j = 0} = {0} := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro h; funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => mul_nonneg (ha i).le (Nat.cast_nonneg (n i)))).1 h i (Finset.mem_univ _)
        rcases mul_eq_zero.1 this with h1 | h1
        · exact absurd h1 (ha i).ne'
        · exact_mod_cast h1
      · rintro rfl; simp [En, oscillatorEnergy]
    have hterm : ∀ n, -(gibbsProbability En 0 n * Real.logb 2 (gibbsProbability En 0 n)) = 0 := by
      intro n
      unfold gibbsProbability
      rw [if_pos rfl, hground, Set.ncard_singleton]
      split_ifs <;> simp
    unfold gibbsEntropy
    simp only [hterm, tsum_zero]
    exact hRHS0
  · set β := gibbsInverseTemperature En E with hβdef
    have hβ0 : 0 ≤ β := Real.sInf_nonneg (fun x hx => hx.1.le)
    have hprob : ∀ n, gibbsProbability En E n = exp (-β * En n) / ∑' j, exp (-β * En j) := by
      intro n; unfold gibbsProbability; rw [if_neg hEpos.ne']; rfl
    unfold gibbsEntropy
    simp_rw [hprob]
    rcases hβ0.eq_or_lt with hβz | hβpos
    · have hZ : ∑' j : Fin ell → ℕ, exp (-β * En j) = 0 := by
        rw [← hβz]; simp only [zero_mul, neg_zero, exp_zero]
        exact tsum_eq_zero_of_not_summable (by rw [summable_const_iff]; norm_num)
      simp only [hZ, div_zero, zero_mul, neg_zero, tsum_zero]
      exact hRHS0
    · set b' := (ell : ℝ) / E with hb'def
      have hb' : 0 < b' := by positivity
      have hg := X6P15g.gibbs_bound En hEn hs β b' hβpos hb' hne
      have hm := X6P15g.mean_le En hEn hs hne E β hβpos rfl
      have hZ'le : ∑' j, exp (-b' * En j) ≤ ∏ i, (1 - exp (-b' * a i))⁻¹ :=
        tsum_le_of_sum_le (fun j => (exp_pos _).le) (X6P15g.box a ha b' hb')
      have hZ'pos := X6P15g.tsum_exp_pos En b' (hs b' hb') hne
      have hfac : ∀ i, 0 < 1 - exp (-b' * a i) := by
        intro i; rw [sub_pos]; have := ha i
        calc exp (-b' * a i) < exp 0 := exp_lt_exp.2 (by nlinarith)
          _ = 1 := exp_zero
      have hlogZ : log (∑' j, exp (-b' * En j)) ≤ ∑ i, log (1 + E / (ell * a i)) := by
        calc log (∑' j, exp (-b' * En j)) ≤ log (∏ i, (1 - exp (-b' * a i))⁻¹) :=
              log_le_log hZ'pos hZ'le
          _ = ∑ i, log ((1 - exp (-b' * a i))⁻¹) :=
              Real.log_prod (fun i _ => (inv_pos.2 (hfac i)).ne')
          _ ≤ ∑ i, log (1 + E / (ell * a i)) := by
              refine Finset.sum_le_sum fun i _ => log_le_log (inv_pos.2 (hfac i)) ?_
              have := X6P15g.inv_bound (b' * a i) (mul_pos hb' (ha i))
              rw [neg_mul] at *
              convert this using 2
              rw [hb'def]; field_simp
      have hconv : ∀ n, -((exp (-β * En n) / ∑' j, exp (-β * En j)) *
          Real.logb 2 (exp (-β * En n) / ∑' j, exp (-β * En j))) =
          -((exp (-β * En n) / ∑' j, exp (-β * En j)) *
            log (exp (-β * En n) / ∑' j, exp (-β * En j))) / log 2 := by
        intro n; rw [Real.logb]; ring
      simp_rw [hconv]
      rw [tsum_div_const]
      have hU : b' * ∑' i, (exp (-β * En i) / ∑' j, exp (-β * En j)) * En i ≤ ell := by
        calc _ ≤ b' * E := by gcongr
          _ = ell := by rw [hb'def]; field_simp
      rw [div_le_iff₀ hlog2, add_mul, Finset.sum_mul, Real.logb, log_exp]
      have : ∀ i, Real.logb 2 (1 + E / (↑ell * a i)) * log 2 = log (1 + E / (ell * a i)) := by
        intro i; rw [Real.logb]; field_simp
      simp_rw [this]
      rw [show (ell : ℝ) * (1 / log 2) * log 2 = ell by field_simp]
      linarith

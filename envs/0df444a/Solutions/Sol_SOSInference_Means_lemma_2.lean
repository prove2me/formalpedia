-- Prove2me | solution 1 for SOSInference.Means.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:35:43.187326+00:00
-- url     : https://prove2.me/submissions/195f1d29-4d2e-4882-894b-48681f60b855

import Mathlib
import Definitions.Def_SOSInference_Means_Tarr
import Definitions.Def_SOSInference_Means_tauLaw

open SOSInference.Means
open MeasureTheory ProbabilityTheory

namespace SOSPoisAux

/-- `V_l = π^{l/2}/Γ(l/2+1)`, the volume of the unit ball. -/
noncomputable def Vl (l : ℕ) : ℝ := Real.pi ^ ((l : ℝ) / 2) / Real.Gamma ((l : ℝ) / 2 + 1)

lemma Vl_pos (l : ℕ) : 0 < Vl l := by
  unfold Vl
  have hG : 0 < Real.Gamma ((l : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpi : 0 < Real.pi ^ ((l : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  positivity

lemma vol_closedBall {l : ℕ} (hl : 1 ≤ l) (y : E l) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall y r) = ENNReal.ofReal (Vl l * r ^ l) := by
  haveI : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold Vl
  have : Real.sqrt Real.pi ^ l = Real.pi ^ ((l : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    ring_nf
  rw [this]; ring

lemma lipschitz_of_bound {l : ℕ} {f : E l → ℝ} {K : ℝ} (hd : Differentiable ℝ f)
    (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K) (x y : E l) : |f y - f x| ≤ K * ‖y - x‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ) (fun z _ => hd z)
    (fun z _ => hK z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa [Real.norm_eq_abs] using this

/-- A nonnegative Lipschitz probability density on `ℝ^l` (`l ≥ 1`) is bounded. -/
lemma density_bounded {l : ℕ} (hl : 1 ≤ l) {f : E l → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hlip : ∀ x y, |f y - f x| ≤ K * ‖y - x‖)
    (hint : ∫⁻ x, ENNReal.ofReal (f x) = 1) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ x, f x ≤ F := by
  set F0 : ℝ := 2 ^ (l + 1) * (K + 1) ^ l / Vl l
  refine ⟨max 1 F0, le_trans zero_le_one (le_max_left _ _), fun x => ?_⟩
  by_contra hcon
  push Not at hcon
  set Mx := f x
  have hM1 : 1 < Mx := lt_of_le_of_lt (le_max_left _ _) hcon
  have hMF : F0 < Mx := lt_of_le_of_lt (le_max_right _ _) hcon
  set ρ := Mx / (2 * (K + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hball : ∀ y ∈ Metric.closedBall x ρ, Mx / 2 ≤ f y := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have h1 := hlip x y
    have h2 : K * ‖y - x‖ ≤ K * ρ := mul_le_mul_of_nonneg_left hy hK0
    have h3 : K * ρ ≤ Mx / 2 := by
      rw [hρ]
      have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      calc K * (Mx / (2 * (K + 1))) = (K / (K + 1)) * (Mx / 2) := by field_simp
        _ ≤ 1 * (Mx / 2) := by gcongr
        _ = Mx / 2 := one_mul _
    have := (abs_le.mp h1).1
    linarith
  have hlow : ENNReal.ofReal (Mx / 2) * volume (Metric.closedBall x ρ) ≤ 1 := by
    rw [← hint, ← setLIntegral_const]
    calc ∫⁻ _ in Metric.closedBall x ρ, ENNReal.ofReal (Mx / 2)
        ≤ ∫⁻ y in Metric.closedBall x ρ, ENNReal.ofReal (f y) := by
          apply setLIntegral_mono' measurableSet_closedBall
          intro y hy; exact ENNReal.ofReal_le_ofReal (hball y hy)
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) := setLIntegral_le_lintegral _ _
  rw [vol_closedBall hl x hρ0.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_one] at hlow
  -- (M/2) * V * (M/(2(K+1)))^l ≤ 1  contradicts  M > F0, M > 1
  have hV := Vl_pos l
  have hpow : Mx ≤ Mx ^ l := by
    calc Mx = Mx ^ 1 := (pow_one _).symm
      _ ≤ Mx ^ l := pow_le_pow_right₀ hM1.le hl
  have e : Mx / 2 * (Vl l * ρ ^ l) = Mx * Mx ^ l * Vl l / (2 ^ (l + 1) * (K + 1) ^ l) := by
    rw [hρ, div_pow, mul_pow, pow_succ]; field_simp
  rw [e, div_le_one (by positivity)] at hlow
  have hF0 : F0 * Vl l = 2 ^ (l + 1) * (K + 1) ^ l := by
    simp only [F0]; field_simp
  have : F0 * Vl l < Mx * Mx ^ l * Vl l := by
    have h1 : F0 < Mx * Mx ^ l := by
      have : Mx < Mx * Mx ^ l := by
        have : 1 < Mx ^ l := lt_of_lt_of_le hM1 hpow
        nlinarith
      linarith
    exact mul_lt_mul_of_pos_right h1 hV
  linarith

/-- Ball estimate: `|μ_f(B(a,r)) − f(a) V r^l| ≤ K r · V r^l`. -/
lemma ball_estimate {l : ℕ} (hl : 1 ≤ l) {f : E l → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f) (hcont : Continuous f)
    (hlip : ∀ x y, |f y - f x| ≤ K * ‖y - x‖) (a : E l) {r : ℝ} (hr : 0 ≤ r) :
    |(lawOfDensity f (Metric.closedBall a r)).toReal - f a * (Vl l * r ^ l)| ≤
      K * r * (Vl l * r ^ l) := by
  have hvol := vol_closedBall hl a hr
  have hfin : volume (Metric.closedBall a r) < ⊤ := by rw [hvol]; exact ENNReal.ofReal_lt_top
  have hint : IntegrableOn f (Metric.closedBall a r) volume :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall a r)
  have hlaw : (lawOfDensity f (Metric.closedBall a r)).toReal =
      ∫ y in Metric.closedBall a r, f y := by
    unfold lawOfDensity
    rw [withDensity_apply _ measurableSet_closedBall,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
        hfm.aestronglyMeasurable]
  rw [hlaw]
  have hconst : f a * (Vl l * r ^ l) = ∫ _ in Metric.closedBall a r, f a := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, hvol,
      ENNReal.toReal_ofReal (by have := Vl_pos l; positivity)]
    ring
  rw [hconst, ← integral_sub hint (integrableOn_const hfin.ne)]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun y => f y - f a)
    (C := K * r) hfin (fun y hy => by
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      rw [Real.norm_eq_abs]
      exact (hlip a y).trans (mul_le_mul_of_nonneg_left hy hK0))
  rw [Real.norm_eq_abs, measureReal_def, hvol,
    ENNReal.toReal_ofReal (by have := Vl_pos l; positivity)] at this
  exact this

/-- `|a^k − b^k| ≤ k|a − b|` on `[0,1]`. -/
lemma pow_sub_pow_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k : ℕ) :
    |a ^ k - b ^ k| ≤ k * |a - b| := by
  have := abs_pow_sub_pow_le a b k
  have hm : max |a| |b| ^ (k - 1) ≤ 1 := by
    apply pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
    rw [abs_of_nonneg ha0, abs_of_nonneg hb0]; exact max_le ha1 hb1
  calc |a ^ k - b ^ k| ≤ |a - b| * k * max |a| |b| ^ (k - 1) := this
    _ ≤ |a - b| * k * 1 := by gcongr
    _ = k * |a - b| := by ring

lemma exp_lip {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| := by
  wlog huv : u ≤ v generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]; exact this hv hu (le_of_not_ge huv)
  have h1 : Real.exp (-v) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 - (v - u) ≤ Real.exp (-(v - u)) := by
    have := Real.add_one_le_exp (-(v - u)); linarith
  have h4 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h5 := Real.exp_pos (-u)
  rw [h2]; nlinarith

/-- Binomial-to-Poisson: `|(1−p)^k − e^{−A}| ≤ k p² + |k p − A|` for `p ∈ [0,1]`, `A ≥ 0`. -/
lemma binom_poisson {p A : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hA : 0 ≤ A) (k : ℕ) :
    |(1 - p) ^ k - Real.exp (-A)| ≤ k * p ^ 2 + |k * p - A| := by
  have he1 : |Real.exp (-p) - 1 - (-p)| ≤ (-p) ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le (by rw [abs_neg, abs_of_nonneg hp0]; exact hp1)
  have hexp0 : 0 ≤ Real.exp (-p) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1 := pow_sub_pow_le (a := 1 - p) (b := Real.exp (-p)) (by linarith) (by linarith)
    hexp0 hexp1 k
  have hpk : Real.exp (-p) ^ k = Real.exp (-(k * p)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hpk] at h1
  have h2 : |1 - p - Real.exp (-p)| ≤ p ^ 2 := by
    rw [show 1 - p - Real.exp (-p) = -(Real.exp (-p) - 1 - (-p)) by ring, abs_neg]
    simpa using he1
  have h3 := exp_lip (u := k * p) (v := A) (by positivity) hA
  calc |(1 - p) ^ k - Real.exp (-A)|
      ≤ |(1 - p) ^ k - Real.exp (-(k * p))| + |Real.exp (-(k * p)) - Real.exp (-A)| :=
        abs_sub_le _ _ _
    _ ≤ k * |1 - p - Real.exp (-p)| + |k * p - A| := add_le_add h1 h3
    _ ≤ k * p ^ 2 + |k * p - A| := by gcongr

lemma prod_approx {a b c d : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hc1 : |c| ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  have : a * b - c * d = a * (b - d) + (a - c) * d := by ring
  rw [this]
  calc |a * (b - d) + (a - c) * d| ≤ |a * (b - d)| + |(a - c) * d| := abs_add_le _ _
    _ = |a| * |b - d| + |a - c| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |b - d| + |a - c| * 1 := by
        gcongr
        · rw [abs_of_nonneg ha0]; exact ha1
        · rw [abs_of_nonneg hd0]; exact hd1
    _ = |a - c| + |b - d| := by ring

end SOSPoisAux

namespace SOSPoisAux

variable {l : ℕ} (M : Model l) (hM : M.Standing)

include hM in
lemma Z_meas (k : ℕ ⊕ ℕ) : Measurable (Sum.elim M.X M.Y k) := by
  cases k with
  | inl a => exact hM.measurable_X a
  | inr b => exact hM.measurable_Y b

include hM in
/-- Conditioning on `X_i`: independence factorization. -/
lemma factor (n m i : ℕ) (hi : i < n) (S : Set (E l × E l)) (hS : MeasurableSet S) :
    M.P {ω | ∀ k ∈ ((Finset.range n).erase i).disjSum (Finset.range m),
        (M.X i ω, Sum.elim M.X M.Y k ω) ∈ S} =
      ∫⁻ x, (lawOfDensity M.fX (Prod.mk x ⁻¹' S)) ^ (n - 1) *
        (lawOfDensity M.fY (Prod.mk x ⁻¹' S)) ^ m ∂(lawOfDensity M.fX) := by
  classical
  set J := ((Finset.range n).erase i).disjSum (Finset.range m) with hJ
  set I0 : Finset (ℕ ⊕ ℕ) := {Sum.inl i} with hI0
  have hdisj : Disjoint I0 J := by
    rw [hI0, Finset.disjoint_singleton_left, hJ, Finset.inl_mem_disjSum]
    simp
  have hind := hM.indep.indepFun_finset I0 J hdisj (Z_meas M hM)
  have hmem0 : Sum.inl i ∈ I0 := by simp [hI0]
  set W : M.Ω → (J → E l) := fun ω k => Sum.elim M.X M.Y k ω with hW
  have hWm : Measurable W := by
    rw [measurable_pi_iff]; intro k; exact Z_meas M hM k
  have hind2 : IndepFun (M.X i) W M.P := by
    have hev : Measurable (fun u : I0 → E l => u ⟨Sum.inl i, hmem0⟩) := measurable_pi_apply _
    have := hind.comp hev measurable_id
    exact this
  have hXm := hM.measurable_X i
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hWm.aemeasurable).mp hind2
  set S' : Set (E l × (J → E l)) := {p | ∀ k : J, (p.1, p.2 k) ∈ S} with hS'
  have hS'm : MeasurableSet S' := by
    have : S' = ⋂ k : J, (fun p : E l × (J → E l) => (p.1, p.2 k)) ⁻¹' S := by
      ext p; simp [hS']
    rw [this]
    exact MeasurableSet.iInter fun k =>
      (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd)) hS
  have hset : {ω | ∀ k ∈ J, (M.X i ω, Sum.elim M.X M.Y k ω) ∈ S} =
      (fun ω => (M.X i ω, W ω)) ⁻¹' S' := by
    ext ω; simp [hS', hW]
  rw [hset, ← Measure.map_apply (hXm.prodMk hWm) hS'm, hjoint, Measure.prod_apply hS'm,
    hM.law_X i]
  apply lintegral_congr
  intro x
  rw [Measure.map_apply hWm (measurable_prodMk_left hS'm)]
  have hpre : W ⁻¹' (Prod.mk x ⁻¹' S') =
      ⋂ k ∈ J, Sum.elim M.X M.Y k ⁻¹' (Prod.mk x ⁻¹' S) := by
    ext ω; simp [hS', hW]
  rw [hpre, hM.indep.measure_inter_preimage_eq_mul J (sets := fun _ => Prod.mk x ⁻¹' S)
    (fun _ _ => measurable_prodMk_left hS), hJ, Finset.prod_disjSum]
  have hX : ∀ k, M.P (M.X k ⁻¹' (Prod.mk x ⁻¹' S)) = lawOfDensity M.fX (Prod.mk x ⁻¹' S) := by
    intro k
    rw [← Measure.map_apply (hM.measurable_X k) (measurable_prodMk_left hS), hM.law_X k]
  have hY : ∀ k, M.P (M.Y k ⁻¹' (Prod.mk x ⁻¹' S)) = lawOfDensity M.fY (Prod.mk x ⁻¹' S) := by
    intro k
    rw [← Measure.map_apply (hM.measurable_Y k) (measurable_prodMk_left hS), hM.law_Y k]
  simp only [Sum.elim_inl, Sum.elim_inr, hX, hY, Finset.prod_const, Finset.card_erase_of_mem
    (Finset.mem_range.mpr hi), Finset.card_range]

end SOSPoisAux

namespace SOSPoisAux

variable {l : ℕ} (M : Model l)

lemma tarr_le_iff (hl : 1 ≤ l) (n : ℕ) (i : Fin n) (lam : E l) (ω : M.Ω) {t : ℝ} (ht : 0 ≤ t) :
    Tarr M n i lam ω ≤ t ↔
      (∃ j, ‖Zfam M n ω j - (M.X i ω + (1 / 2 : ℝ) • lam)‖ ^ 2 ≤
          t ^ ((2 : ℝ) / l) / (n : ℝ) ^ ((2 : ℝ) / l) ∧ Zfam M n ω j ≠ M.X i ω) ∨
        (∀ j, Zfam M n ω j = M.X i ω) := by
  classical
  set D := Zfam M n ω
  set a := M.X i ω + (1 / 2 : ℝ) • lam
  set q : ℝ := (2 : ℝ) / l with hq
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hq0 : 0 < q := by rw [hq]; positivity
  set A := {s : ℝ | 0 ≤ s ∧ 1 ≤ Ncount M n i lam s ω} with hA
  have hAiff : ∀ s, s ∈ A ↔ 0 ≤ s ∧ ∃ j, ‖D j - a‖ ^ 2 ≤ s ^ q / (n : ℝ) ^ q ∧ D j ≠ M.X i ω := by
    intro s
    simp only [hA, Set.mem_setOf_eq, Ncount, Nat.one_le_iff_ne_zero, ne_eq,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies, not_forall,
      not_not, exists_prop]
    rfl
  have hTarr : Tarr M n i lam ω = sInf A := rfl
  have hbdd : BddBelow A := ⟨0, fun s hs => hs.1⟩
  have hmono : ∀ s s', s ∈ A → s ≤ s' → s' ∈ A := by
    intro s s' hs hss'
    rw [hAiff] at hs ⊢
    obtain ⟨hs0, j, hj, hne⟩ := hs
    refine ⟨hs0.trans hss', j, le_trans hj ?_, hne⟩
    gcongr
  have hclosed : IsClosed A := by
    have : A = Set.Ici 0 ∩ ⋃ j ∈ (Finset.univ.filter fun j => D j ≠ M.X i ω),
        {s : ℝ | ‖D j - a‖ ^ 2 ≤ s ^ q / (n : ℝ) ^ q} := by
      ext s
      rw [hAiff]
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨h0, j, h1, h2⟩; exact ⟨h0, j, h2, h1⟩
      · rintro ⟨h0, j, h2, h1⟩; exact ⟨h0, j, h1, h2⟩
    rw [this]
    refine isClosed_Ici.inter (isClosed_biUnion_finset fun j _ => ?_)
    exact isClosed_le continuous_const ((Real.continuous_rpow_const hq0.le).div_const _)
  constructor
  · intro hT
    by_cases hAne : A.Nonempty
    · have hmem : sInf A ∈ A := hclosed.csInf_mem hAne hbdd
      have ht' := hmono _ t hmem (hTarr ▸ hT)
      rw [hAiff] at ht'
      exact Or.inl ht'.2
    · right
      intro j
      by_contra hne
      apply hAne
      have hev := ((tendsto_rpow_atTop hq0).eventually_ge_atTop
        (‖D j - a‖ ^ 2 * (n : ℝ) ^ q)).and (Filter.eventually_ge_atTop 0)
      obtain ⟨s, hs1, hs0⟩ := hev.exists
      have hnq : 0 < (n : ℝ) ^ q := by
        have : 0 < n := Fin.pos i
        exact Real.rpow_pos_of_pos (by exact_mod_cast this) q
      refine ⟨s, (hAiff s).mpr ⟨hs0, j, ?_, hne⟩⟩
      rw [le_div_iff₀ hnq]; exact hs1
  · rintro (⟨j, hj, hne⟩ | hall)
    · rw [hTarr]
      exact csInf_le hbdd ((hAiff t).mpr ⟨ht, j, hj, hne⟩)
    · have hAempty : A = ∅ := by
        ext s
        rw [hAiff]
        simp only [Set.mem_empty_iff_false, iff_false, not_and, not_exists]
        intro _ j _ hne
        exact hne (hall j)
      rw [hTarr, hAempty, Real.sInf_empty]
      exact ht

end SOSPoisAux

namespace SOSPoisAux

/-- The pointwise (conditional on `X_i = x`) Poisson-approximation error. -/
lemma pointwise_bound {n m : ℕ} (hn : 1 ≤ n) {κ V t K r FX FY gX gY fa fb : ℝ} (hκ : 0 ≤ κ)
    (hm1 : (m : ℝ) ≤ κ * n) (hm2 : κ * n - 1 ≤ m) (hV : 0 ≤ V) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hr : 0 ≤ r) (hgX0 : 0 ≤ gX) (hgX1 : gX ≤ 1) (hgY0 : 0 ≤ gY) (hgY1 : gY ≤ 1)
    (hfa : 0 ≤ fa) (hfa' : fa ≤ FX) (hfb : 0 ≤ fb) (hfb' : fb ≤ FY)
    (hX : |gX - fa * (V * (t / n))| ≤ K * r * (V * (t / n)))
    (hY : |gY - fb * (V * (t / n))| ≤ K * r * (V * (t / n))) :
    |Real.exp (-((fa + κ * fb) * V * t)) - (1 - gX) ^ (n - 1) * (1 - gY) ^ m| ≤
      ((FX + K * r) * V * t) ^ 2 / n + (FX + K * r) * V * t / n + K * r * V * t +
      κ * ((FY + K * r) * V * t) ^ 2 / n + (FY + K * r) * V * t / n + κ * (K * r * V * t) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set A := fa * V * t with hA
  set B := κ * fb * V * t with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hsplit : Real.exp (-((fa + κ * fb) * V * t)) = Real.exp (-A) * Real.exp (-B) := by
    rw [← Real.exp_add]; congr 1; rw [hA, hB]; ring
  rw [hsplit, abs_sub_comm]
  have hpa := prod_approx (a := (1 - gX) ^ (n - 1)) (b := (1 - gY) ^ m) (c := Real.exp (-A))
    (d := Real.exp (-B)) (pow_nonneg (by linarith) _) (pow_le_one₀ (by linarith) (by linarith))
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
    (by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.mpr (by linarith))
  refine hpa.trans ?_
  have bX := binom_poisson hgX0 hgX1 hA0 (n - 1)
  have bY := binom_poisson hgY0 hgY1 hB0 m
  -- bounds on gX, gY
  have hgXle : gX ≤ (FX + K * r) * V * t / n := by
    have := (abs_le.mp hX).2
    have h1 : fa * (V * (t / n)) ≤ FX * (V * (t / n)) := by gcongr
    have e : (FX + K * r) * V * t / n = FX * (V * (t / n)) + K * r * (V * (t / n)) := by
      field_simp
    rw [e]; linarith
  have hgYle : gY ≤ (FY + K * r) * V * t / n := by
    have := (abs_le.mp hY).2
    have h1 : fb * (V * (t / n)) ≤ FY * (V * (t / n)) := by gcongr
    have e : (FY + K * r) * V * t / n = FY * (V * (t / n)) + K * r * (V * (t / n)) := by
      field_simp
    rw [e]; linarith
  set βX := (FX + K * r) * V * t with hβX
  set βY := (FY + K * r) * V * t with hβY
  have hβX0 : 0 ≤ βX := by have := hfa.trans hfa'; positivity
  have hβY0 : 0 ≤ βY := by have := hfb.trans hfb'; positivity
  have hn1 : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub hn]; simp
  -- X part
  have eX1 : ((n - 1 : ℕ) : ℝ) * gX ^ 2 ≤ βX ^ 2 / n := by
    rw [hn1]
    have : gX ^ 2 ≤ (βX / n) ^ 2 := pow_le_pow_left₀ hgX0 hgXle 2
    calc (n - 1 : ℝ) * gX ^ 2 ≤ n * (βX / n) ^ 2 := by
          apply mul_le_mul (by linarith) this (by positivity) (by positivity)
      _ = βX ^ 2 / n := by field_simp
  have eX2 : |((n - 1 : ℕ) : ℝ) * gX - A| ≤ βX / n + K * r * V * t := by
    rw [hn1]
    have e : (n - 1 : ℝ) * gX - A = n * (gX - fa * (V * (t / n))) - gX := by
      rw [hA]; field_simp; ring
    rw [e]
    have h1 : |n * (gX - fa * (V * (t / n)))| ≤ K * r * V * t := by
      rw [abs_mul, abs_of_pos hn0]
      calc n * |gX - fa * (V * (t / n))| ≤ n * (K * r * (V * (t / n))) := by gcongr
        _ = K * r * V * t := by field_simp
    calc |n * (gX - fa * (V * (t / n))) - gX| ≤ |n * (gX - fa * (V * (t / n)))| + |gX| :=
          abs_sub _ _
      _ ≤ K * r * V * t + βX / n := by rw [abs_of_nonneg hgX0]; linarith
      _ = βX / n + K * r * V * t := by ring
  -- Y part
  have hmn : (m : ℝ) ≤ κ * n := hm1
  have eY1 : (m : ℝ) * gY ^ 2 ≤ κ * βY ^ 2 / n := by
    have : gY ^ 2 ≤ (βY / n) ^ 2 := pow_le_pow_left₀ hgY0 hgYle 2
    calc (m : ℝ) * gY ^ 2 ≤ (κ * n) * (βY / n) ^ 2 := by
          apply mul_le_mul hmn this (by positivity) (by positivity)
      _ = κ * βY ^ 2 / n := by field_simp
  have eY2 : |(m : ℝ) * gY - B| ≤ βY / n + κ * (K * r * V * t) := by
    have e : (m : ℝ) * gY - B = (m - κ * n) * gY + κ * (n * (gY - fb * (V * (t / n)))) := by
      rw [hB]; field_simp; ring
    rw [e]
    have h1 : |(m - κ * n : ℝ) * gY| ≤ βY / n := by
      rw [abs_mul, abs_of_nonneg hgY0]
      have : |(m - κ * n : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |(m - κ * n : ℝ)| * gY ≤ 1 * gY := by gcongr
        _ ≤ βY / n := by linarith
    have h2 : |κ * (n * (gY - fb * (V * (t / n))))| ≤ κ * (K * r * V * t) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hκ, abs_of_pos hn0]
      apply mul_le_mul_of_nonneg_left _ hκ
      calc n * |gY - fb * (V * (t / n))| ≤ n * (K * r * (V * (t / n))) := by gcongr
        _ = K * r * V * t := by field_simp
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  linarith [bX, bY, eX1, eX2, eY1, eY2]

end SOSPoisAux

namespace SOSPoisAux

variable {l : ℕ} (M : Model l) (hM : M.Standing)

include hM in
lemma Lam_pos' (lam x : E l) : 0 < Lam M x lam := by
  unfold Lam
  have h1 := hM.fX_pos (x + (1 / 2 : ℝ) • lam)
  have h2 := hM.fY_pos (x + (1 / 2 : ℝ) • lam)
  have h3 := hM.kappa_nonneg
  have hG : 0 < Real.Gamma ((l : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpi : 0 < Real.pi ^ ((l : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have : 0 < M.fX (x + (1 / 2 : ℝ) • lam) + M.κ * M.fY (x + (1 / 2 : ℝ) • lam) := by
    nlinarith
  positivity

include hM in
lemma Lam_meas' (lam : E l) : Measurable (fun x => Lam M x lam) := by
  unfold Lam
  have h1 : Measurable (fun x : E l => M.fX (x + (1 / 2 : ℝ) • lam)) :=
    hM.measurable_fX.comp (measurable_id.add_const _)
  have h2 : Measurable (fun x : E l => M.fY (x + (1 / 2 : ℝ) • lam)) :=
    hM.measurable_fY.comp (measurable_id.add_const _)
  exact ((h1.add (h2.const_mul _)).mul_const _).div_const _

lemma expMeasure_meas' {f : E l → ℝ} (hf : Measurable f) :
    Measurable (fun x => expMeasure (f x)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [expMeasure, gammaMeasure]
  simp_rw [withDensity_apply _ hs]
  have : Measurable (fun p : E l × ℝ => gammaPDF 1 (f p.1) p.2) := by
    unfold gammaPDF gammaPDFReal
    apply Measurable.ennreal_ofReal
    apply Measurable.ite (measurableSet_le measurable_const measurable_snd)
    · fun_prop
    · exact measurable_const
  exact this.lintegral_prod_right'

include hM in
lemma tauLaw_Iic' (lam : E l) (t : ℝ) (ht : 0 ≤ t) :
    tauLaw M lam (Set.Iic t) =
      ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(Lam M x lam * t))) ∂(lawX M) := by
  unfold tauLaw
  rw [Measure.bind_apply measurableSet_Iic (expMeasure_meas' (Lam_meas' M hM lam)).aemeasurable]
  apply lintegral_congr
  intro x
  have hr := Lam_pos' M hM lam x
  haveI := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr t
  rw [cdf_eq_real, if_pos ht] at h
  rw [← h, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma lawOfDensity_prob {f : E l → ℝ} (h : ∫⁻ x, ENNReal.ofReal (f x) = 1) :
    IsProbabilityMeasure (lawOfDensity f) := by
  constructor
  simp only [lawOfDensity]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, h]

lemma lawOfDensity_singleton (hl : 1 ≤ l) (f : E l → ℝ) (x : E l) :
    lawOfDensity f {x} = 0 := by
  have h0 : volume ({x} : Set (E l)) = 0 := by
    have := vol_closedBall hl x (le_refl (0 : ℝ))
    rw [Metric.closedBall_zero] at this
    rw [this]; simp [zero_pow (by omega : l ≠ 0)]
  unfold lawOfDensity
  rw [withDensity_apply _ (measurableSet_singleton x), Measure.restrict_eq_zero.mpr h0,
    lintegral_zero_measure]

end SOSPoisAux

open SOSPoisAux in
theorem solution {l : ℕ} (hl : 1 ≤ l) (M : Model l) (hM : M.Standing) (hreg : M.SmoothDensities)
    (lam : E l) (t : ℝ) (ht : 0 < t) (i : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ hi : i < n,
      |(M.P {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t}).toReal - ((tauLaw M lam) (Set.Iic t)).toReal| ≤
        C * t ^ (1 + 1 / (l : ℝ)) / (n : ℝ) ^ (1 / (l : ℝ)) := by
  classical
  obtain ⟨hdX, hdY, K, hK⟩ := hreg
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0).1
  have lipX := lipschitz_of_bound hdX (fun x => (hK x).1)
  have lipY := lipschitz_of_bound hdY (fun x => (hK x).2)
  obtain ⟨FX, hFX0, hFX⟩ := density_bounded hl hK0 lipX hM.lintegral_fX
  obtain ⟨FY, hFY0, hFY⟩ := density_bounded hl hK0 lipY hM.lintegral_fY
  haveI hPX : IsProbabilityMeasure (lawOfDensity M.fX) := lawOfDensity_prob hM.lintegral_fX
  haveI hPY : IsProbabilityMeasure (lawOfDensity M.fY) := lawOfDensity_prob hM.lintegral_fY
  set V := Vl l with hVdef
  have hV : 0 < V := Vl_pos l
  set κ := M.κ with hκdef
  have hκ : 0 ≤ κ := hM.kappa_nonneg
  set c : E l := (1 / 2 : ℝ) • lam with hc
  set s : ℝ := 1 / (l : ℝ) with hs
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by rw [hs, div_le_one hl']; exact_mod_cast hl
  set r1 : ℝ := t ^ s with hr1
  have hr10 : 0 ≤ r1 := by positivity
  set βX0 := (FX + K * r1) * V * t
  set βY0 := (FY + K * r1) * V * t
  set C1 : ℝ := βX0 ^ 2 + βX0 + K * r1 * V * t + κ * βY0 ^ 2 + βY0 + κ * (K * r1 * V * t)
    with hC1
  have hC10 : 0 ≤ C1 := by positivity
  have hts : 0 < t ^ (1 + s) := Real.rpow_pos_of_pos ht _
  refine ⟨(C1 + 1) / t ^ (1 + s), ?_⟩
  intro n hi
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hns : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos (by linarith) s
  have hRHS : (C1 + 1) / t ^ (1 + s) * t ^ (1 + s) / (n : ℝ) ^ s = (C1 + 1) / (n : ℝ) ^ s := by
    field_simp
  rw [hRHS]
  -- the tauLaw CDF
  set e : E l → ℝ := fun x => Real.exp (-(Lam M x lam * t)) with he
  have he_meas : Measurable e := ((Lam_meas' M hM lam).mul_const _).neg.exp
  have he01 : ∀ x, 0 ≤ e x ∧ e x ≤ 1 := by
    intro x
    have := Lam_pos' M hM lam x
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  have hint_e : Integrable e (lawOfDensity M.fX) :=
    Integrable.of_bound he_meas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (he01 x).1]; exact (he01 x).2)
  have htau : ((tauLaw M lam) (Set.Iic t)).toReal = 1 - ∫ x, e x ∂(lawOfDensity M.fX) := by
    rw [tauLaw_Iic' M hM lam t ht.le]
    have : lawX M = lawOfDensity M.fX := rfl
    rw [this, ← integral_eq_lintegral_of_nonneg_ae]
    · rw [integral_sub (integrable_const _) hint_e, integral_const]; simp
    · exact Filter.Eventually.of_forall fun x => by
        have := (he01 x).2; simp only [Pi.zero_apply]; linarith
    · exact (he_meas.const_sub _).aestronglyMeasurable
  have htau01 : ((tauLaw M lam) (Set.Iic t)).toReal ≤ 1 ∧ 0 ≤ ((tauLaw M lam) (Set.Iic t)).toReal := by
    refine ⟨?_, ENNReal.toReal_nonneg⟩
    rw [htau]
    have : 0 ≤ ∫ x, e x ∂(lawOfDensity M.fX) := integral_nonneg fun x => (he01 x).1
    linarith
  have hP01 : (M.P {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t}).toReal ≤ 1 := by
    have := prob_le_one (μ := M.P) (s := {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t})
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have hP0 : 0 ≤ (M.P {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t}).toReal := ENNReal.toReal_nonneg
  by_cases hn : n = 1
  · subst hn
    simp only [Nat.cast_one, Real.one_rpow, div_one]
    rw [abs_le]; constructor <;> linarith [htau01.1, htau01.2]
  have hn2 : 2 ≤ n := by omega
  set m := mOf M.κ n with hm
  set r : ℝ := (t / n) ^ s with hr
  have htn : 0 ≤ t / n := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hrl : r ^ l = t / n := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul htn, hs, one_div_mul_cancel hl'.ne',
      Real.rpow_one]
  have hrr1 : r = r1 / (n : ℝ) ^ s := by
    rw [hr, hr1, Real.div_rpow ht.le (by linarith)]
  have hR : t ^ ((2 : ℝ) / l) / (n : ℝ) ^ ((2 : ℝ) / l) = r ^ 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul htn, Real.div_rpow ht.le (by linarith)]
    congr 2 <;> (rw [hs]; push_cast; ring)
  -- the product set
  set S : Set (E l × E l) := {p | p.2 = p.1 ∨ ¬ ‖p.2 - (p.1 + c)‖ ^ 2 ≤ r ^ 2} with hS
  have hSm : MeasurableSet S := by
    apply (measurableSet_eq_fun measurable_snd measurable_fst).union
    apply MeasurableSet.compl
    exact measurableSet_le ((measurable_snd.sub (measurable_fst.add_const c)).norm.pow_const 2)
      measurable_const
  set Dg : Set (E l × E l) := {p | p.2 = p.1} with hDg
  have hDgm : MeasurableSet Dg := measurableSet_eq_fun measurable_snd measurable_fst
  set J := ((Finset.range n).erase i).disjSum (Finset.range m) with hJ
  set Z := Sum.elim M.X M.Y with hZ
  set G := {ω | ∀ k ∈ J, (M.X i ω, Z k ω) ∈ S} with hG
  set Nset := {ω | ∀ k ∈ J, (M.X i ω, Z k ω) ∈ Dg} with hNset
  have hGm : MeasurableSet G := by
    have : G = ⋂ k ∈ J, (fun ω => (M.X i ω, Z k ω)) ⁻¹' S := by ext ω; simp [hG]
    rw [this]
    exact Finset.measurableSet_biInter _ fun k _ =>
      ((hM.measurable_X i).prodMk (Z_meas M hM k)) hSm
  have hfacN := factor M hM n m i hi Dg hDgm
  have hNnull : M.P Nset = 0 := by
    rw [hfacN]
    have : ∀ x : E l, Prod.mk x ⁻¹' Dg = {x} := by intro x; ext y; simp [hDg]
    simp only [this, lawOfDensity_singleton hl]
    rw [zero_pow (by omega : n - 1 ≠ 0)]
    simp
  -- event relations
  have hiff := fun ω => tarr_le_iff M hl n ⟨i, hi⟩ lam ω ht.le
  have hsub1 : Gᶜ ⊆ {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t} := by
    intro ω hω
    simp only [hG, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, exists_prop] at hω
    obtain ⟨k, hkJ, hkS⟩ := hω
    simp only [hS, Set.mem_setOf_eq, not_or, not_not] at hkS
    rw [Set.mem_setOf_eq, hiff, hR]
    left
    rw [hJ, Finset.mem_disjSum] at hkJ
    rcases hkJ with ⟨k', hk', rfl⟩ | ⟨k', hk', rfl⟩
    · have hk'n : k' < n := Finset.mem_range.mp (Finset.mem_of_mem_erase hk')
      exact ⟨Sum.inl ⟨k', hk'n⟩, hkS.2, hkS.1⟩
    · have hk'm : k' < m := Finset.mem_range.mp hk'
      exact ⟨Sum.inr ⟨k', hk'm⟩, hkS.2, hkS.1⟩
  have hsub2 : {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t} ⊆ Gᶜ ∪ Nset := by
    intro ω hω
    rw [Set.mem_setOf_eq, hiff, hR] at hω
    rcases hω with ⟨j, hj1, hj2⟩ | hall
    · left
      simp only [hG, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, exists_prop]
      rcases j with ⟨j', hj'⟩ | ⟨j', hj'⟩
      · refine ⟨Sum.inl j', ?_, ?_⟩
        · rw [hJ, Finset.inl_mem_disjSum, Finset.mem_erase, Finset.mem_range]
          refine ⟨fun h => hj2 ?_, hj'⟩
          subst h; rfl
        · simp only [hS, Set.mem_setOf_eq, not_or, not_not]
          exact ⟨hj2, hj1⟩
      · refine ⟨Sum.inr j', ?_, ?_⟩
        · rw [hJ, Finset.inr_mem_disjSum, Finset.mem_range]; exact hj'
        · simp only [hS, Set.mem_setOf_eq, not_or, not_not]
          exact ⟨hj2, hj1⟩
    · right
      simp only [hNset, Set.mem_setOf_eq, hDg]
      intro k hk
      rw [hJ, Finset.mem_disjSum] at hk
      rcases hk with ⟨k', hk', rfl⟩ | ⟨k', hk', rfl⟩
      · have hk'n : k' < n := Finset.mem_range.mp (Finset.mem_of_mem_erase hk')
        exact hall (Sum.inl ⟨k', hk'n⟩)
      · have hk'm : k' < m := Finset.mem_range.mp hk'
        exact hall (Sum.inr ⟨k', hk'm⟩)
  have hPT : M.P {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t} = 1 - M.P G := by
    rw [← prob_compl_eq_one_sub hGm]
    apply le_antisymm
    · calc M.P {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t} ≤ M.P (Gᶜ ∪ Nset) := measure_mono hsub2
        _ ≤ M.P Gᶜ + M.P Nset := measure_union_le _ _
        _ = M.P Gᶜ := by rw [hNnull, add_zero]
    · exact measure_mono hsub1
  -- sections of S
  set Bset : Set (E l × E l) := {p | dist p.2 (p.1 + c) ≤ r} with hBset
  have hBm : MeasurableSet Bset :=
    measurableSet_le (measurable_snd.dist (measurable_fst.add_const c)) measurable_const
  have hBsec : ∀ x : E l, Prod.mk x ⁻¹' Bset = Metric.closedBall (x + c) r := by
    intro x; ext y; simp [hBset, Metric.mem_closedBall]
  have hSsec : ∀ (f : E l → ℝ), IsProbabilityMeasure (lawOfDensity f) → ∀ x : E l,
      lawOfDensity f (Prod.mk x ⁻¹' S) =
        ENNReal.ofReal (1 - (lawOfDensity f (Metric.closedBall (x + c) r)).toReal) := by
    intro f hf x
    have hset : Prod.mk x ⁻¹' S = (Metric.closedBall (x + c) r \ {x})ᶜ := by
      ext y
      simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_diff,
        Metric.mem_closedBall, dist_eq_norm, Set.mem_singleton_iff]
      rw [sq_le_sq₀ (norm_nonneg _) hr0]
      tauto
    rw [hset, prob_compl_eq_one_sub (measurableSet_closedBall.diff (measurableSet_singleton x)),
      measure_diff_null (lawOfDensity_singleton hl f x)]
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  set gX : E l → ℝ := fun x => (lawOfDensity M.fX (Metric.closedBall (x + c) r)).toReal with hgX
  set gY : E l → ℝ := fun x => (lawOfDensity M.fY (Metric.closedBall (x + c) r)).toReal with hgY
  have hgXm : Measurable gX := by
    have := (measurable_measure_prodMk_left (ν := lawOfDensity M.fX) hBm).ennreal_toReal
    simpa only [hBsec] using this
  have hgYm : Measurable gY := by
    have := (measurable_measure_prodMk_left (ν := lawOfDensity M.fY) hBm).ennreal_toReal
    simpa only [hBsec] using this
  have hgX01 : ∀ x, 0 ≤ gX x ∧ gX x ≤ 1 := fun x =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)⟩
  have hgY01 : ∀ x, 0 ≤ gY x ∧ gY x ≤ 1 := fun x =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)⟩
  set hGf : E l → ℝ := fun x => (1 - gX x) ^ (n - 1) * (1 - gY x) ^ m with hGfdef
  have hGfm : Measurable hGf :=
    ((hgXm.const_sub 1).pow_const _).mul ((hgYm.const_sub 1).pow_const _)
  have hGf01 : ∀ x, 0 ≤ hGf x ∧ hGf x ≤ 1 := by
    intro x
    have h1 := hgX01 x; have h2 := hgY01 x
    exact ⟨mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _),
      mul_le_one₀ (pow_le_one₀ (by linarith) (by linarith)) (pow_nonneg (by linarith) _)
        (pow_le_one₀ (by linarith) (by linarith))⟩
  have hint_G : Integrable hGf (lawOfDensity M.fX) :=
    Integrable.of_bound hGfm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hGf01 x).1]; exact (hGf01 x).2)
  have hPG : (M.P G).toReal = ∫ x, hGf x ∂(lawOfDensity M.fX) := by
    rw [hG, factor M hM n m i hi S hSm]
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (hGf01 x).1)
      hGfm.aestronglyMeasurable]
    congr 1
    apply lintegral_congr
    intro x
    rw [hSsec _ hPX x, hSsec _ hPY x, hGfdef]
    dsimp only
    rw [ENNReal.ofReal_mul (pow_nonneg (by linarith [(hgX01 x).2]) _),
      ENNReal.ofReal_pow (by linarith [(hgX01 x).2]), ENNReal.ofReal_pow (by linarith [(hgY01 x).2])]
  have hPTr : (M.P {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t}).toReal = 1 - ∫ x, hGf x ∂(lawOfDensity M.fX) := by
    rw [hPT, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, hPG]
  rw [hPTr, htau]
  have hdiff : 1 - ∫ x, hGf x ∂(lawOfDensity M.fX) - (1 - ∫ x, e x ∂(lawOfDensity M.fX)) =
      ∫ x, (e x - hGf x) ∂(lawOfDensity M.fX) := by
    rw [integral_sub hint_e hint_G]; ring
  rw [hdiff]
  -- pointwise bound
  have hm1 : (m : ℝ) ≤ κ * n := Nat.floor_le (by positivity)
  have hm2 : κ * n - 1 ≤ m := (Nat.sub_one_lt_floor (κ * n)).le
  have hns1 : (1 : ℝ) ≤ (n : ℝ) ^ s := Real.one_le_rpow hnR hs0.le
  have hnsn : (n : ℝ) ^ s ≤ n := by
    have := Real.rpow_le_rpow_of_exponent_le hnR hs1
    rwa [Real.rpow_one] at this
  have hrle : r ≤ r1 := by
    rw [hrr1]; exact div_le_self hr10 hns1
  have hpt : ∀ x, |e x - hGf x| ≤ C1 / (n : ℝ) ^ s := by
    intro x
    have hbX := ball_estimate hl hK0 (fun y => (hM.fX_pos y).le) hM.measurable_fX
      hdX.continuous lipX (x + c) hr0
    have hbY := ball_estimate hl hK0 (fun y => (hM.fY_pos y).le) hM.measurable_fY
      hdY.continuous lipY (x + c) hr0
    rw [hrl] at hbX hbY
    have hLam : Lam M x lam = (M.fX (x + c) + κ * M.fY (x + c)) * V := by
      simp only [Lam, hVdef, Vl, hc, hκdef]; ring
    have hpb := pointwise_bound (n := n) (m := m) hn1 hκ hm1 hm2 hV.le ht.le hK0 hr0
      (hgX01 x).1 (hgX01 x).2 (hgY01 x).1 (hgY01 x).2 (hM.fX_pos _).le (hFX (x + c))
      (hM.fY_pos _).le (hFY (x + c)) hbX hbY
    have hex : e x = Real.exp (-((M.fX (x + c) + κ * M.fY (x + c)) * V * t)) := by
      simp only [he, hLam]
    rw [hex]
    refine hpb.trans ?_
    -- compare with C1 / n^s
    have hβX : (FX + K * r) * V * t ≤ βX0 := by
      have : K * r ≤ K * r1 := mul_le_mul_of_nonneg_left hrle hK0
      have : FX + K * r ≤ FX + K * r1 := by linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hV.le) ht.le
    have hβY : (FY + K * r) * V * t ≤ βY0 := by
      have : K * r ≤ K * r1 := mul_le_mul_of_nonneg_left hrle hK0
      have : FY + K * r ≤ FY + K * r1 := by linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hV.le) ht.le
    have hβX0 : 0 ≤ (FX + K * r) * V * t := by positivity
    have hβY0 : 0 ≤ (FY + K * r) * V * t := by positivity
    have hinv : 1 / (n : ℝ) ≤ 1 / (n : ℝ) ^ s := one_div_le_one_div_of_le hns hnsn
    have t1 : ((FX + K * r) * V * t) ^ 2 / n ≤ βX0 ^ 2 / (n : ℝ) ^ s := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div (βX0 ^ 2)]
      exact mul_le_mul (pow_le_pow_left₀ hβX0 hβX 2) hinv (by positivity) (by positivity)
    have t2 : (FX + K * r) * V * t / n ≤ βX0 / (n : ℝ) ^ s := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div βX0]
      exact mul_le_mul hβX hinv (by positivity) (by positivity)
    have t4 : κ * ((FY + K * r) * V * t) ^ 2 / n ≤ κ * βY0 ^ 2 / (n : ℝ) ^ s := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div (κ * βY0 ^ 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβY0 hβY 2) hκ) hinv
        (by positivity) (by positivity)
    have t5 : (FY + K * r) * V * t / n ≤ βY0 / (n : ℝ) ^ s := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div βY0]
      exact mul_le_mul hβY hinv (by positivity) (by positivity)
    have t3 : K * r * V * t = K * r1 * V * t / (n : ℝ) ^ s := by rw [hrr1]; ring
    have hsum : C1 / (n : ℝ) ^ s = βX0 ^ 2 / (n : ℝ) ^ s + βX0 / (n : ℝ) ^ s +
        K * r1 * V * t / (n : ℝ) ^ s + κ * βY0 ^ 2 / (n : ℝ) ^ s + βY0 / (n : ℝ) ^ s +
        κ * (K * r1 * V * t / (n : ℝ) ^ s) := by
      rw [hC1]; ring
    rw [hsum, t3]
    linarith
  have hbound := norm_integral_le_of_norm_le_const (μ := lawOfDensity M.fX)
    (f := fun x => e x - hGf x) (C := C1 / (n : ℝ) ^ s)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpt x)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at hbound
  refine hbound.trans ?_
  gcongr
  linarith

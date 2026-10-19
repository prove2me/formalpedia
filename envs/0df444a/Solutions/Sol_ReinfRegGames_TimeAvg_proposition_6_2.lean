-- Prove2me | solution 1 for ReinfRegGames.TimeAvg.proposition_6_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T08:15:01.137393+00:00
-- url     : https://prove2.me/submissions/547b85e4-40c5-4ece-a716-58f1f3c3879e

-- Licensed under Apache 2.0. Full zero-sum learning time-average theorem.
import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_TimeAvg_TimeAverage


open Finset
open ReinfRegGames.Extinction

namespace TimeAvgProof

variable {B : Type*} [Fintype B]

lemma simplex_nonempty_type {x : B → ℝ} (hx : x ∈ stdSimplex ℝ B) : Nonempty B := by
  by_contra h
  have : IsEmpty B := not_nonempty_iff.mp h
  have hs := hx.2
  simp at hs

lemma norm_sq_le_sqDist [Nonempty B] (x z : B → ℝ) : ‖x-z‖^2 ≤ sqDist x z := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun a : B => ‖(x-z) a‖₊)
  have he : ‖x-z‖ = |x a-z a| := by
    change ((Finset.univ.sup (fun b : B => ‖(x-z) b‖₊) : NNReal) : ℝ) = _
    rw [ha]
    exact Real.norm_eq_abs (x a-z a)
  rw [he, sq_abs]
  exact Finset.single_le_sum (fun b _ => sq_nonneg (x b-z b)) (Finset.mem_univ a)

lemma abs_dot_le (x z : B → ℝ) : |x ⬝ᵥ z| ≤ Fintype.card B * ‖x‖ * ‖z‖ := by
  calc
    |x ⬝ᵥ z| ≤ ∑ a, |x a*z a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : B, ‖x‖ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x a)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z a) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

lemma choice_strong_comparison {h : (B → ℝ) → ℝ} {K : ℝ}
    (hp : IsPenalty h K) {y y' x x' : B → ℝ}
    (hx : IsChoice h y x) (hx' : IsChoice h y' x') :
    K / 2 * sqDist x x' ≤ (y-y') ⬝ᵥ (x-x') := by
  let m := (1/2:ℝ) • x + (1/2:ℝ) • x'
  have hm : m ∈ stdSimplex ℝ B := convex_stdSimplex ℝ B hx.1 hx'.1
    (by norm_num) (by norm_num) (by norm_num)
  have hc := hp.2.2.2 x hx.1 x' hx'.1 (1/2) (by norm_num)
  have h1 := hx.2 m hm
  have h2 := hx'.2 m hm
  have hy : y ⬝ᵥ m = (y ⬝ᵥ x)/2 + (y ⬝ᵥ x')/2 := by
    simp only [m, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib]
    simp_rw [show ∀ a b : ℝ, a * ((1 / 2) * b) = (a*b)/2 by intros; ring]
    rw [← Finset.sum_div, ← Finset.sum_div]
  have hy' : y' ⬝ᵥ m = (y' ⬝ᵥ x)/2 + (y' ⬝ᵥ x')/2 := by
    simp only [m, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib]
    simp_rw [show ∀ a b : ℝ, a * ((1 / 2) * b) = (a*b)/2 by intros; ring]
    rw [← Finset.sum_div, ← Finset.sum_div]
  have he : (y-y') ⬝ᵥ (x-x') = y ⬝ᵥ x-y ⬝ᵥ x'-(y' ⬝ᵥ x-y' ⬝ᵥ x') := by
    simp only [dotProduct, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  norm_num only at hc
  change h m ≤ _ at hc
  rw [hy] at h1
  rw [hy'] at h2
  rw [he]
  nlinarith

lemma choice_norm_bound {h : (B → ℝ) → ℝ} {K : ℝ}
    (hp : IsPenalty h K) {y y' x x' : B → ℝ}
    (hx : IsChoice h y x) (hx' : IsChoice h y' x') :
    ‖x-x'‖ ≤ (2 * Fintype.card B / K) * ‖y-y'‖ := by
  have : Nonempty B := simplex_nonempty_type hx.1
  have hK := hp.2.2.1
  have hs := choice_strong_comparison hp hx hx'
  have hn := norm_sq_le_sqDist x x'
  have hd := (le_abs_self ((y-y') ⬝ᵥ (x-x'))).trans (abs_dot_le (y-y') (x-x'))
  have hb : K/2 * ‖x-x'‖^2 ≤ (Fintype.card B : ℝ)*‖y-y'‖*‖x-x'‖ :=
    (mul_le_mul_of_nonneg_left hn (by positivity)).trans (hs.trans hd)
  by_cases hz : ‖x-x'‖ = 0
  · rw [hz]; positivity
  · have hzpos : 0 < ‖x-x'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hc : (K/2*‖x-x'‖)*‖x-x'‖ ≤
        ((Fintype.card B:ℝ)*‖y-y'‖)*‖x-x'‖ := by nlinarith [hb]
    have hh := (mul_le_mul_iff_left₀ hzpos).mp hc
    have hbnd : ‖x-x'‖ ≤ (2*Fintype.card B*‖y-y'‖)/K :=
      (le_div_iff₀ hK).mpr (by nlinarith [hh])
    convert hbnd using 1
    ring

lemma choice_unique {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K)
    {y x x' : B → ℝ} (hx : IsChoice h y x) (hx' : IsChoice h y x') : x=x' := by
  have hb := choice_norm_bound hp hx hx'
  simpa only [sub_self, norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] using hb

end TimeAvgProof


open Set Filter Finset
open ReinfRegGames.Extinction

namespace TimeAvgProof

variable {B : Type*} [Fintype B] [Nonempty B]

lemma exists_choice {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K) (y : B → ℝ) :
    ∃ x, IsChoice h y x := by
  classical
  have hs : (stdSimplex ℝ B).Nonempty := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary B)⟩
  have hc : ContinuousOn (fun x => y ⬝ᵥ x - h x) (stdSimplex ℝ B) :=
    (by fun_prop : Continuous (fun x : B → ℝ => y ⬝ᵥ x)).continuousOn.sub hp.1
  obtain ⟨x, hx, hmax⟩ := (isCompact_stdSimplex ℝ B).exists_isMaxOn hs hc
  exact ⟨x, hx, hmax⟩

noncomputable def choice {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K) (y : B → ℝ) : B → ℝ :=
  Classical.choose (exists_choice hp y)

lemma choice_spec {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K) (y : B → ℝ) :
    IsChoice h y (choice hp y) := Classical.choose_spec (exists_choice hp y)

lemma choice_continuous {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K) :
    Continuous (choice hp) := by
  have hc : 0 ≤ 2 * (Fintype.card B : ℝ) / K := by
    have := hp.2.2.1
    positivity
  have hl : LipschitzWith ⟨2 * Fintype.card B / K, hc⟩ (choice hp) :=
    lipschitzWith_iff_norm_sub_le.mpr fun y z => choice_norm_bound hp (choice_spec hp y) (choice_spec hp z)
  exact hl.continuous

lemma choices_continuousOn {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K)
    {y x : ℝ → B → ℝ} (hy : ContinuousOn y (Ici 0))
    (hx : ∀ t ∈ Ici (0 : ℝ), IsChoice h (y t) (x t)) : ContinuousOn x (Ici 0) := by
  apply ((choice_continuous hp).comp_continuousOn hy).congr
  intro t ht
  exact choice_unique hp (hx t ht) (choice_spec hp (y t))

omit [Nonempty B] in
lemma conj_eq_choice {h : (B → ℝ) → ℝ} {y x : B → ℝ} (hx : IsChoice h y x) :
    conj h y = y ⬝ᵥ x - h x := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hx.2 z hz

omit [Nonempty B] in
lemma fenchel_nonneg {h : (B → ℝ) → ℝ} {y x p : B → ℝ}
    (hx : IsChoice h y x) (hp : p ∈ stdSimplex ℝ B) : 0 ≤ fenchelCoupling h p y := by
  unfold fenchelCoupling
  rw [conj_eq_choice hx]
  have := hx.2 p hp
  linarith

end TimeAvgProof


open Set Filter Finset
open ReinfRegGames.Extinction

namespace TimeAvgProof

variable {B : Type*} [Fintype B]

noncomputable def dotCLM (x : B → ℝ) : (B → ℝ) →L[ℝ] ℝ :=
  ∑ a : B, x a • ContinuousLinearMap.proj a

lemma dotCLM_apply (x v : B → ℝ) : dotCLM x v = v ⬝ᵥ x := by
  simp only [dotCLM, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma conj_remainder_bounds {h : (B → ℝ) → ℝ} {y y' x x' : B → ℝ}
    (hx : IsChoice h y x) (hx' : IsChoice h y' x') :
    0 ≤ conj h y' - conj h y - (y'-y) ⬝ᵥ x ∧
    conj h y' - conj h y - (y'-y) ⬝ᵥ x ≤ (y'-y) ⬝ᵥ (x'-x) := by
  rw [conj_eq_choice hx, conj_eq_choice hx']
  have h1 := hx.2 x' hx'.1
  have h2 := hx'.2 x hx.1
  simp only [sub_dotProduct, dotProduct_sub]
  constructor <;> linarith

lemma conjugate_hasFDerivAt [Nonempty B] {h : (B → ℝ) → ℝ} {K : ℝ}
    (hp : IsPenalty h K) (y : B → ℝ) :
    HasFDerivAt (conj h) (dotCLM (choice hp y)) y := by
  let c : ℝ := 2 * Fintype.card B / K
  have hc : 0 ≤ c := by have := hp.2.2.1; dsimp [c]; positivity
  let D : ℝ := Fintype.card B * c
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hc
  have hb : ∀ v : B → ℝ,
      ‖conj h (y+v)-conj h y-dotCLM (choice hp y) v‖ ≤ D * ‖v‖^2 := by
    intro v
    have hs := conj_remainder_bounds (choice_spec hp y) (choice_spec hp (y+v))
    have hl := choice_norm_bound hp (choice_spec hp (y+v)) (choice_spec hp y)
    simp only [add_sub_cancel_left] at hs hl
    rw [dotCLM_apply, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc
      _ ≤ |v ⬝ᵥ (choice hp (y+v)-choice hp y)| := hs.2.trans (le_abs_self _)
      _ ≤ Fintype.card B * ‖v‖ * ‖choice hp (y+v)-choice hp y‖ := abs_dot_le _ _
      _ ≤ Fintype.card B * ‖v‖ * (c * ‖v‖) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ = D * ‖v‖^2 := by dsimp [D]; ring
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hd : 0 < ε / (D+1) := div_pos hε (by positivity)
  have hball : ∀ᶠ v : B → ℝ in nhds 0, v ∈ Metric.ball (0 : B → ℝ) (ε/(D+1)) :=
    Metric.ball_mem_nhds (0 : B → ℝ) hd
  have hevent : ∀ᶠ v : B → ℝ in nhds 0, ‖v‖ < ε / (D+1) :=
    hball.mono (fun v hv => by
      simpa only [Metric.mem_ball, dist_zero_right] using hv)
  filter_upwards [hevent] with v hv
  have hsmall : D * ‖v‖ ≤ ε := by
    have := (lt_div_iff₀ (show 0 < D+1 by positivity)).mp hv
    nlinarith [norm_nonneg v]
  exact (hb v).trans (by nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)])

lemma conjugate_hasFDerivAt_of_choice {h : (B → ℝ) → ℝ} {K : ℝ}
    (hp : IsPenalty h K) {y x : B → ℝ} (hx : IsChoice h y x) :
    HasFDerivAt (conj h) (dotCLM x) y := by
  have : Nonempty B := simplex_nonempty_type hx.1
  have he := choice_unique hp (choice_spec hp y) hx
  simpa only [he] using conjugate_hasFDerivAt hp y

end TimeAvgProof


open Set Filter Finset MeasureTheory
open ReinfRegGames.Extinction

namespace TimeAvgProof

variable {B : Type*} [Fintype B]

lemma scalar_regret {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K)
    (y x v : ℝ → B → ℝ)
    (hx : ∀ t ∈ Ici (0 : ℝ), IsChoice h (y t) (x t))
    (hy : ∀ t ∈ Ici (0 : ℝ), ∀ a,
      HasDerivWithinAt (fun s => y s a) (v t a) (Ici 0) t)
    (hv : ContinuousOn v (Ici 0))
    (p : B → ℝ) (hp' : p ∈ stdSimplex ℝ B) {T : ℝ} (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, ∑ a, v s a * (p a-x s a)) ≤ fenchelCoupling h p (y 0) := by
  have : Nonempty B := simplex_nonempty_type hp'
  have hyd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt y (v t) (Ici 0) t :=
    fun t ht => hasDerivWithinAt_pi.mpr (hy t ht)
  have hyc : ContinuousOn y (Ici 0) := fun t ht => (hyd t ht).continuousWithinAt
  have hxc := choices_continuousOn hp hyc hx
  let f : ℝ → ℝ := fun t => y t ⬝ᵥ p - conj h (y t)
  let g : ℝ → ℝ := fun t => ∑ a, v t a * (p a-x t a)
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt f (g t) (Ici 0) t := by
    intro t ht
    have h1 := (dotCLM p).hasFDerivAt.comp_hasDerivWithinAt t (hyd t ht)
    have h2 := (conjugate_hasFDerivAt_of_choice hp (hx t ht)).comp_hasDerivWithinAt t (hyd t ht)
    have he : g t = v t ⬝ᵥ p - v t ⬝ᵥ x t := by
      simp only [g, dotProduct, mul_sub, Finset.sum_sub_distrib]
    have hh := h1.sub h2
    simp only [Function.comp_def, dotCLM_apply] at hh
    rw [he]
    convert hh using 1 <;> rfl
  have hgc : ContinuousOn g (Ici 0) := by
    apply continuousOn_finsetSum
    intro a _
    exact (continuous_apply a |>.comp_continuousOn hv).mul
      (continuousOn_const.sub (continuous_apply a |>.comp_continuousOn hxc))
  have hgi : IntervalIntegrable g volume 0 T :=
    (hgc.mono (by rw [uIcc_of_le hT.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  have hfc : ContinuousOn f (Ici 0) := fun t ht => (hd t ht).continuousWithinAt
  have hftc : (∫ s in (0 : ℝ)..T, g s) = f T-f 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT.le
    · exact hfc.mono Icc_subset_Ici_self
    · intro t ht
      exact (hd t ht.1.le).mono (fun s hs => le_trans ht.1.le hs.le)
    · exact hgi
  change (∫ s in (0 : ℝ)..T, g s) ≤ _
  rw [hftc]
  have hn := fenchel_nonneg (hx T hT.le) hp'
  dsimp [f, fenchelCoupling] at hn ⊢
  linarith

end TimeAvgProof


open Finset
open ReinfRegGames.Extinction

namespace TimeAvgProof

variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

noncomputable def purePair (a : A 0) (b : A 1) : ∀ k, A k :=
  (piFinTwoEquiv A).symm (a, b)

noncomputable def bilinearPayoff (u : Fin 2 → (∀ k, A k) → ℝ)
    (k : Fin 2) (p : A 0 → ℝ) (q : A 1 → ℝ) : ℝ :=
  ∑ a, ∑ b, p a * q b * u k (purePair a b)

omit [∀ k, DecidableEq (A k)] in
theorem expectedPayoff_eq (u : Fin 2 → (∀ k, A k) → ℝ)
    (x : ∀ k, A k → ℝ) (k : Fin 2) :
    AGT.expectedPayoff u x k = bilinearPayoff u k (x 0) (x 1) := by
  classical
  unfold AGT.expectedPayoff AGT.profileProb bilinearPayoff
  rw [← (piFinTwoEquiv A).symm.sum_comp]
  simp [Fintype.sum_prod_type, Fin.prod_univ_two, purePair]

theorem payoffVec_zero (u : Fin 2 → (∀ k, A k) → ℝ)
    (x : ∀ k, A k → ℝ) (a : A 0) :
    payoffVec u x 0 a = ∑ b, x 1 b * u 0 (purePair a b) := by
  classical
  rw [payoffVec, expectedPayoff_eq]
  simp [bilinearPayoff, Pi.single_apply]

theorem payoffVec_one (u : Fin 2 → (∀ k, A k) → ℝ)
    (x : ∀ k, A k → ℝ) (b : A 1) :
    payoffVec u x 1 b = ∑ a, x 0 a * u 1 (purePair a b) := by
  classical
  rw [payoffVec, expectedPayoff_eq]
  simp [bilinearPayoff, Pi.single_apply]

theorem deviation_zero (u : Fin 2 → (∀ k, A k) → ℝ)
    (x : ∀ k, A k → ℝ) (p : A 0 → ℝ) :
    (∑ a, payoffVec u x 0 a * p a) =
      AGT.expectedPayoff u (Function.update x 0 p) 0 := by
  classical
  simp only [payoffVec_zero, expectedPayoff_eq, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), bilinearPayoff]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem deviation_one (u : Fin 2 → (∀ k, A k) → ℝ)
    (x : ∀ k, A k → ℝ) (p : A 1 → ℝ) :
    (∑ b, payoffVec u x 1 b * p b) =
      AGT.expectedPayoff u (Function.update x 1 p) 1 := by
  classical
  simp only [payoffVec_one, expectedPayoff_eq, Function.update_self,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), bilinearPayoff]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem current_payoff (u : Fin 2 → (∀ k, A k) → ℝ)
    (x : ∀ k, A k → ℝ) (k : Fin 2) :
    (∑ a, payoffVec u x k a * x k a) = AGT.expectedPayoff u x k := by
  fin_cases k
  · simpa using deviation_zero u x (x 0)
  · simpa using deviation_one u x (x 1)

omit [∀ k, DecidableEq (A k)] in
theorem zero_sum_expected (u : Fin 2 → (∀ k, A k) → ℝ)
    (hzs : ∀ s, u 0 s + u 1 s = 0) (x : ∀ k, A k → ℝ) :
    AGT.expectedPayoff u x 0 + AGT.expectedPayoff u x 1 = 0 := by
  unfold AGT.expectedPayoff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro s _
  rw [← mul_add, hzs, mul_zero]

omit [∀ k, DecidableEq (A k)] in
theorem continuous_expectedPayoff (u : Fin 2 → (∀ k, A k) → ℝ) (k : Fin 2) :
    Continuous (fun x : ∀ k, A k → ℝ => AGT.expectedPayoff u x k) := by
  unfold AGT.expectedPayoff AGT.profileProb
  fun_prop

theorem continuous_payoffVec (u : Fin 2 → (∀ k, A k) → ℝ) (k : Fin 2) (a : A k) :
    Continuous (fun x : ∀ k, A k → ℝ => payoffVec u x k a) := by
  unfold payoffVec AGT.expectedPayoff AGT.profileProb
  fun_prop

end TimeAvgProof


open Finset Set MeasureTheory
open ReinfRegGames.Extinction ReinfRegGames.TimeAvg

namespace TimeAvgProof

variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

omit [∀ k, DecidableEq (A k)] [∀ k, Fintype (A k)] in
theorem coordinate_intervalIntegrable {x : ℝ → ∀ k, A k → ℝ}
    (hx : ContinuousOn x (Ici 0)) {T : ℝ} (hT : 0 ≤ T) (k : Fin 2) (a : A k) :
    IntervalIntegrable (fun s => x s k a) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  exact ((continuous_apply a).comp_continuousOn
    ((continuous_apply k).comp_continuousOn hx)).mono (by
      simpa [uIcc_of_le hT] using (Icc_subset_Ici_self : Icc (0 : ℝ) T ⊆ Ici 0))

omit [∀ k, DecidableEq (A k)] in
theorem timeAvg_profile {x : ℝ → ∀ k, A k → ℝ}
    (hx : ContinuousOn x (Ici 0))
    (hprofile : ∀ t, 0 ≤ t → AGT.IsMixedProfile (x t)) {T : ℝ} (hT : 0 < T) :
    AGT.IsMixedProfile (timeAvg x T) := by
  intro k
  constructor
  · intro a
    exact mul_nonneg (inv_nonneg.mpr hT.le)
      (intervalIntegral.integral_nonneg hT.le (fun s hs => (hprofile s hs.1 k).1 a))
  · unfold timeAvg
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum
      (fun a _ => coordinate_intervalIntegrable hx hT.le k a)]
    have heq : (∫ s in (0 : ℝ)..T, ∑ a, x s k a) = T := by
      calc
        _ = ∫ s in (0 : ℝ)..T, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hs0 : 0 ≤ s := (by simpa only [uIcc_of_le hT.le] using hs : s ∈ Icc (0 : ℝ) T).1
          exact (hprofile s hs0 k).2
        _ = T := by simp
    rw [heq, inv_mul_cancel₀ hT.ne']

omit [∀ k, DecidableEq (A k)] in
theorem compact_profiles : IsCompact {x : ∀ k, A k → ℝ | AGT.IsMixedProfile x} := by
  have heq : {x : ∀ k, A k → ℝ | AGT.IsMixedProfile x} =
      Set.pi Set.univ (fun k => stdSimplex ℝ (A k)) := by
    ext x
    simp [AGT.IsMixedProfile, AGT.IsLottery, stdSimplex, Set.mem_pi]
  rw [heq]
  exact isCompact_univ_pi (fun k => isCompact_stdSimplex ℝ (A k))

omit [∀ k, DecidableEq (A k)] in
theorem average_bilinear_zero (u : Fin 2 → (∀ k, A k) → ℝ)
    {x : ℝ → ∀ k, A k → ℝ} (hx : ContinuousOn x (Ici 0))
    (p : A 0 → ℝ) {T : ℝ} (hT : 0 < T) :
    bilinearPayoff u 0 p (timeAvg x T 1) =
      T⁻¹ * ∫ s in (0 : ℝ)..T, bilinearPayoff u 0 p (x s 1) := by
  unfold bilinearPayoff timeAvg
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_finsetSum
      (fun b _ => ((coordinate_intervalIntegrable hx hT.le 1 b).const_mul _).mul_const _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro a _
    convert IntervalIntegrable.sum Finset.univ (fun b _ =>
      ((coordinate_intervalIntegrable hx hT.le 1 b).const_mul (p a)).mul_const (u 0 (purePair a b))) using 1 <;> first | rfl | (ext s; simp)

omit [∀ k, DecidableEq (A k)] in
theorem average_bilinear_one (u : Fin 2 → (∀ k, A k) → ℝ)
    {x : ℝ → ∀ k, A k → ℝ} (hx : ContinuousOn x (Ici 0))
    (q : A 1 → ℝ) {T : ℝ} (hT : 0 < T) :
    bilinearPayoff u 1 (timeAvg x T 0) q =
      T⁻¹ * ∫ s in (0 : ℝ)..T, bilinearPayoff u 1 (x s 0) q := by
  unfold bilinearPayoff timeAvg
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_finsetSum
      (fun b _ => ((coordinate_intervalIntegrable hx hT.le 0 _).mul_const _).mul_const _),
      intervalIntegral.integral_mul_const]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro a _
    convert IntervalIntegrable.sum (Finset.univ : Finset (A 1)) (fun b _ =>
      ((coordinate_intervalIntegrable hx hT.le 0 a).mul_const (q b)).mul_const (u 1 (purePair a b))) using 1 <;> first | rfl | (ext s; simp)

end TimeAvgProof


open Filter Topology Set

namespace TimeAvgProof

theorem compact_distance_convergence {X : Type*} [MetricSpace X]
    {K S : Set X} (hK : IsCompact K) {f : ℝ → X}
    (hmem : ∀ t, 0 < t → f t ∈ K)
    (hcluster : ∀ (t : ℕ → ℝ), Tendsto t atTop atTop →
      ∀ z, Tendsto (f ∘ t) atTop (𝓝 z) → z ∈ S) :
    Tendsto (fun t => Metric.infDist (f t) S) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  by_contra h
  push Not at h
  obtain ⟨ε, hε, hbad⟩ := h
  choose t ht hdist using fun n : ℕ => hbad ((n : ℝ) + 1)
  have htpos (n : ℕ) : 0 < t n := by have := ht n; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have htlim : Tendsto t atTop atTop :=
    tendsto_atTop_mono (fun n => by have := ht n; linarith)
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun n => hmem (t n) (htpos n))
  have hzS := hcluster (t ∘ φ) (htlim.comp hφ.tendsto_atTop) z hlim
  have hzero : Tendsto (fun n => dist (f (t (φ n))) z) atTop (𝓝 0) := by
    simpa only [Function.comp_def, dist_self] using hlim.dist (tendsto_const_nhds (x := z))
  have hlower : ∀ n, ε ≤ dist (f (t (φ n))) z := by
    intro n
    have hh := hdist (φ n)
    have hnn := Metric.infDist_nonneg (x := f (t (φ n))) (s := S)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hh
    exact hh.trans (Metric.infDist_le_dist_of_mem hzS)
  exact (not_le_of_gt hε) (ge_of_tendsto hzero (Eventually.of_forall hlower))

end TimeAvgProof


open Filter Topology Set Finset
open ReinfRegGames.TimeAvg

namespace TimeAvgProof

variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] 

theorem cluster_isNash (u : Fin 2 → (∀ k, A k) → ℝ)
    (hzs : ∀ s, u 0 s + u 1 s = 0)
    {f : ℝ → ∀ k, A k → ℝ}
    (hmem : ∀ t, 0 < t → AGT.IsMixedProfile (f t))
    (hpair : ∀ p : A 0 → ℝ, AGT.IsLottery p → ∀ q : A 1 → ℝ,
      AGT.IsLottery q → ∃ C : ℝ, ∀ t, 0 < t →
      AGT.expectedPayoff u (Function.update (f t) 0 p) 0 +
      AGT.expectedPayoff u (Function.update (f t) 1 q) 1 ≤ C / t)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) (z : ∀ k, A k → ℝ)
    (hz : Tendsto (f ∘ t) atTop (𝓝 z)) : AGT.IsMixedNash u z := by
  have hpos : ∀ᶠ n in atTop, 0 < t n := ht.eventually (eventually_gt_atTop 0)
  have hzmem : AGT.IsMixedProfile z := compact_profiles.isClosed.mem_of_tendsto hz
    (hpos.mono (fun n hn => hmem (t n) hn))
  have hpq (p : A 0 → ℝ) (hp : AGT.IsLottery p)
      (q : A 1 → ℝ) (hq : AGT.IsLottery q) :
      AGT.expectedPayoff u (Function.update z 0 p) 0 +
      AGT.expectedPayoff u (Function.update z 1 q) 1 ≤ 0 := by
    obtain ⟨C, hC⟩ := hpair p hp q hq
    have hc0 : Continuous (fun w : ∀ k, A k → ℝ =>
        AGT.expectedPayoff u (Function.update w 0 p) 0) := by
      exact (continuous_expectedPayoff u 0).comp (by fun_prop)
    have hc1 : Continuous (fun w : ∀ k, A k → ℝ =>
        AGT.expectedPayoff u (Function.update w 1 q) 1) := by
      exact (continuous_expectedPayoff u 1).comp (by fun_prop)
    have hleft := ((hc0.add hc1).tendsto z).comp hz
    have hright : Tendsto (fun n => C / t n) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
        tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ht)
    exact le_of_tendsto_of_tendsto hleft hright (hpos.mono fun n hn => hC (t n) hn)
  refine ⟨hzmem, ?_⟩
  intro k p hp
  fin_cases k
  · change AGT.expectedPayoff u (Function.update z 0 p) 0 ≤ AGT.expectedPayoff u z 0
    have hh := hpq p hp (z 1) (hzmem 1)
    simp only [Function.update_eq_self] at hh
    have hzero := zero_sum_expected u hzs z
    linarith
  · change AGT.expectedPayoff u (Function.update z 1 p) 1 ≤ AGT.expectedPayoff u z 1
    have hh := hpq (z 0) (hzmem 0) p hp
    simp only [Function.update_eq_self] at hh
    have hzero := zero_sum_expected u hzs z
    linarith

theorem convergence_of_pair_regret (u : Fin 2 → (∀ k, A k) → ℝ)
    (hzs : ∀ s, u 0 s + u 1 s = 0)
    {f : ℝ → ∀ k, A k → ℝ}
    (hmem : ∀ t, 0 < t → AGT.IsMixedProfile (f t))
    (hpair : ∀ p : A 0 → ℝ, AGT.IsLottery p → ∀ q : A 1 → ℝ,
      AGT.IsLottery q → ∃ C : ℝ, ∀ t, 0 < t →
      AGT.expectedPayoff u (Function.update (f t) 0 p) 0 +
      AGT.expectedPayoff u (Function.update (f t) 1 q) 1 ≤ C / t) :
    Tendsto (fun t => Metric.infDist (f t) {z | AGT.IsMixedNash u z}) atTop (𝓝 0) := by
  exact compact_distance_convergence compact_profiles hmem
    (cluster_isNash u hzs hmem hpair)

end TimeAvgProof


open Set Filter Finset MeasureTheory
open ReinfRegGames.Extinction ReinfRegGames.TimeAvg

namespace TimeAvgProof

variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

theorem orbit_continuous (u : Fin 2 → (∀ k, A k) → ℝ)
    (h : ∀ k, (A k → ℝ) → ℝ) (K : Fin 2 → ℝ)
    (hpen : ∀ k, IsPenalty (h k) (K k))
    {y x : ℝ → ∀ k, A k → ℝ} (horb : IsRLOrbit u h y x) :
    ContinuousOn x (Ici 0) := by
  apply continuousOn_pi.mpr
  intro k
  have : Nonempty (A k) := simplex_nonempty_type (horb 0 le_rfl k).1.1
  have hy : ContinuousOn (fun t => y t k) (Ici 0) := by
    apply continuousOn_pi.mpr
    intro a t ht
    exact ((horb t ht k).2 a).continuousWithinAt
  exact choices_continuousOn (hpen k) hy (fun t ht => (horb t ht k).1)

theorem orbit_profiles (u : Fin 2 → (∀ k, A k) → ℝ)
    (h : ∀ k, (A k → ℝ) → ℝ)
    {y x : ℝ → ∀ k, A k → ℝ} (horb : IsRLOrbit u h y x)
    (t : ℝ) (ht : 0 ≤ t) : AGT.IsMixedProfile (x t) := by
  intro k
  exact (horb t ht k).1.1

theorem orbit_payoff_continuous (u : Fin 2 → (∀ k, A k) → ℝ)
    {x : ℝ → ∀ k, A k → ℝ} (hx : ContinuousOn x (Ici 0)) (k : Fin 2) :
    ContinuousOn (fun t a => payoffVec u (x t) k a) (Ici 0) := by
  apply continuousOn_pi.mpr
  intro a
  exact (continuous_payoffVec u k a).comp_continuousOn hx

end TimeAvgProof


open Set Finset MeasureTheory
open ReinfRegGames.Extinction ReinfRegGames.TimeAvg

namespace TimeAvgProof

variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

noncomputable def regretIntegrand (u : Fin 2 → (∀ k, A k) → ℝ)
    (x : ℝ → ∀ k, A k → ℝ) (k : Fin 2) (p : A k → ℝ) (t : ℝ) : ℝ :=
  ∑ a, payoffVec u (x t) k a * (p a - x t k a)

theorem regretIntegrand_continuous (u : Fin 2 → (∀ k, A k) → ℝ)
    {x : ℝ → ∀ k, A k → ℝ} (hx : ContinuousOn x (Ici 0))
    (k : Fin 2) (p : A k → ℝ) :
    ContinuousOn (regretIntegrand u x k p) (Ici 0) := by
  have hc : Continuous (fun w : ∀ k, A k → ℝ =>
      ∑ a, payoffVec u w k a * (p a - w k a)) := by
    unfold payoffVec AGT.expectedPayoff AGT.profileProb
    fun_prop
  exact hc.comp_continuousOn hx

theorem regret_pair_identity (u : Fin 2 → (∀ k, A k) → ℝ)
    (hzs : ∀ s, u 0 s + u 1 s = 0)
    (x : ℝ → ∀ k, A k → ℝ) (p : A 0 → ℝ) (q : A 1 → ℝ) (t : ℝ) :
    regretIntegrand u x 0 p t + regretIntegrand u x 1 q t =
      bilinearPayoff u 0 p (x t 1) + bilinearPayoff u 1 (x t 0) q := by
  unfold regretIntegrand
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [deviation_zero, deviation_one, current_payoff, current_payoff]
  have hz := zero_sum_expected u hzs (x t)
  simp only [expectedPayoff_eq, Function.update_self, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)] at hz ⊢
  linarith

theorem pair_average_bound (u : Fin 2 → (∀ k, A k) → ℝ)
    (hzs : ∀ s, u 0 s + u 1 s = 0)
    {x : ℝ → ∀ k, A k → ℝ} (hx : ContinuousOn x (Ici 0))
    (p : A 0 → ℝ) (q : A 1 → ℝ) {C D T : ℝ} (hT : 0 < T)
    (hp : (∫ t in (0 : ℝ)..T, regretIntegrand u x 0 p t) ≤ C)
    (hq : (∫ t in (0 : ℝ)..T, regretIntegrand u x 1 q t) ≤ D) :
    AGT.expectedPayoff u (Function.update (timeAvg x T) 0 p) 0 +
    AGT.expectedPayoff u (Function.update (timeAvg x T) 1 q) 1 ≤ (C + D) / T := by
  have hi (k : Fin 2) (r : A k → ℝ) :
      IntervalIntegrable (regretIntegrand u x k r) volume 0 T :=
    ((regretIntegrand_continuous u hx k r).mono (by
      simpa only [uIcc_of_le hT.le] using
        (Icc_subset_Ici_self : Icc (0 : ℝ) T ⊆ Ici 0))).intervalIntegrable
  have hi0 : IntervalIntegrable (fun t => bilinearPayoff u 0 p (x t 1)) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mono (s := Ici (0 : ℝ))
    · have hc : Continuous (fun w : ∀ k, A k → ℝ => bilinearPayoff u 0 p (w 1)) := by
        unfold bilinearPayoff
        fun_prop
      exact hc.comp_continuousOn hx
    · simpa only [uIcc_of_le hT.le] using
        (Icc_subset_Ici_self : Icc (0 : ℝ) T ⊆ Ici 0)
  have hi1 : IntervalIntegrable (fun t => bilinearPayoff u 1 (x t 0) q) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mono (s := Ici (0 : ℝ))
    · have hc : Continuous (fun w : ∀ k, A k → ℝ => bilinearPayoff u 1 (w 0) q) := by
        unfold bilinearPayoff
        fun_prop
      exact hc.comp_continuousOn hx
    · simpa only [uIcc_of_le hT.le] using
        (Icc_subset_Ici_self : Icc (0 : ℝ) T ⊆ Ici 0)
  have hsum : (∫ t in (0 : ℝ)..T, bilinearPayoff u 0 p (x t 1)) +
      (∫ t in (0 : ℝ)..T, bilinearPayoff u 1 (x t 0) q) ≤ C + D := by
    rw [← intervalIntegral.integral_add hi0 hi1]
    simp_rw [← regret_pair_identity u hzs x p q]
    rw [intervalIntegral.integral_add (hi 0 p) (hi 1 q)]
    exact add_le_add hp hq
  rw [expectedPayoff_eq, expectedPayoff_eq]
  simp only [Function.update_self, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  rw [average_bilinear_zero u hx p hT, average_bilinear_one u hx q hT, ← mul_add,
    div_eq_mul_inv, mul_comm (C + D)]
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hT.le)

end TimeAvgProof


namespace ReinfRegGames.TimeAvg

open TimeAvgProof ReinfRegGames.Extinction

theorem timeavg_complete {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : Fin 2 → (∀ k, A k) → ℝ) (hzs : ∀ s, u 0 s + u 1 s = 0)
    (xstar : ∀ k, A k → ℝ) (_hNash : AGT.IsMixedNash u xstar) (_hint : ∀ k α, 0 < xstar k α)
    (h : ∀ k, (A k → ℝ) → ℝ) (K : Fin 2 → ℝ) (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x) :
    Filter.Tendsto (fun t => Metric.infDist (timeAvg x t) {z | AGT.IsMixedNash u z})
      Filter.atTop (nhds 0) := by
  have hxc := orbit_continuous u h K hpen horb
  apply convergence_of_pair_regret u hzs
  · intro t ht
    exact timeAvg_profile hxc (orbit_profiles u h horb) ht
  · intro p hp q hq
    refine ⟨fenchelCoupling (h 0) p (y 0 0) + fenchelCoupling (h 1) q (y 0 1), ?_⟩
    intro T hT
    apply pair_average_bound u hzs hxc p q hT
    · exact scalar_regret (hpen 0) (fun t => y t 0) (fun t => x t 0)
        (fun t => payoffVec u (x t) 0) (fun t ht => (horb t ht 0).1)
        (fun t ht a => by simpa only [one_mul] using (horb t ht 0).2 a)
        (orbit_payoff_continuous u hxc 0) p hp hT
    · exact scalar_regret (hpen 1) (fun t => y t 1) (fun t => x t 1)
        (fun t => payoffVec u (x t) 1) (fun t ht => (horb t ht 1).1)
        (fun t ht a => by simpa only [one_mul] using (horb t ht 1).2 a)
        (orbit_payoff_continuous u hxc 1) q hq hT

end ReinfRegGames.TimeAvg


namespace ReinfRegGames.TimeAvg

theorem proposition_6_2 {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : Fin 2 → (∀ k, A k) → ℝ) (hzs : ∀ s, u 0 s + u 1 s = 0)
    (xstar : ∀ k, A k → ℝ) (hNash : AGT.IsMixedNash u xstar) (hint : ∀ k α, 0 < xstar k α)
    (h : ∀ k, (A k → ℝ) → ℝ) (K : Fin 2 → ℝ) (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x) :
    Filter.Tendsto (fun t => Metric.infDist (timeAvg x t) {z | AGT.IsMixedNash u z})
      Filter.atTop (nhds 0) := by
  exact timeavg_complete u hzs xstar hNash hint h K hpen y x horb

end ReinfRegGames.TimeAvg

open ReinfRegGames.TimeAvg

theorem solution {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : Fin 2 → (∀ k, A k) → ℝ) (hzs : ∀ s, u 0 s + u 1 s = 0)
    (xstar : ∀ k, A k → ℝ) (hNash : AGT.IsMixedNash u xstar) (hint : ∀ k α, 0 < xstar k α)
    (h : ∀ k, (A k → ℝ) → ℝ) (K : Fin 2 → ℝ) (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x) :
    Filter.Tendsto (fun t => Metric.infDist (timeAvg x t) {z | AGT.IsMixedNash u z})
      Filter.atTop (nhds 0) := ReinfRegGames.TimeAvg.proposition_6_2 u hzs xstar hNash hint h K hpen y x horb

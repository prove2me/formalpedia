-- Prove2me | solution 1 for WFMFG.Conv.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:44:49.234734+00:00
-- url     : https://prove2.me/submissions/b80572ce-c5b1-4cab-b2ae-cfd5ad9db249

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset WFMFG.Conv

namespace WFMFG49

lemma line_hasDerivAt {d : ℕ} (h : (Fin d → ℝ) → ℝ) (p0 w : Fin d → ℝ)
    (hp0 : ∑ i, p0 i = 1) (hw : ∑ i, w i = 0) (s0 : ℝ)
    (hd : DifferentiableWithinAt ℝ h (affPlane d) (p0 + s0 • w)) :
    HasDerivAt (fun s : ℝ => h (p0 + s • w))
      (fderivWithin ℝ h (affPlane d) (p0 + s0 • w) w) s0 := by
  have hline : HasDerivAt (fun s : ℝ => p0 + s • w) w s0 := by
    simpa using ((hasDerivAt_id s0).smul_const w).const_add p0
  have hmaps : Set.MapsTo (fun s : ℝ => p0 + s • w) Set.univ (affPlane d) := by
    intro s _
    simp only [affPlane, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hp0, hw]
    ring
  have := hd.hasFDerivWithinAt.comp_hasDerivWithinAt s0 hline.hasDerivWithinAt hmaps
  rw [hasDerivWithinAt_univ] at this
  exact this

lemma lineDeriv_eq {d : ℕ} (h : (Fin d → ℝ) → ℝ) (p w : Fin d → ℝ)
    (hp : ∑ i, p i = 1) (hw : ∑ i, w i = 0)
    (hd : DifferentiableWithinAt ℝ h (affPlane d) p) :
    lineDeriv ℝ h p w = fderivWithin ℝ h (affPlane d) p w := by
  have hd' : DifferentiableWithinAt ℝ h (affPlane d) (p + (0:ℝ) • w) := by simpa using hd
  have := line_hasDerivAt h p w hp hw 0 hd'
  simp only [zero_smul, add_zero] at this
  exact HasLineDerivAt.lineDeriv this

lemma sum_single_sub {d : ℕ} (i m : Fin d) :
    ∑ k, (Pi.single i (1:ℝ) - Pi.single m 1 : Fin d → ℝ) k = 0 := by
  simp [Finset.sum_sub_distrib]

lemma sD_sub {d : ℕ} [NeZero d] (h : (Fin d → ℝ) → ℝ) (p : Fin d → ℝ)
    (hp : ∑ i, p i = 1) (hd : DifferentiableWithinAt ℝ h (affPlane d) p) (j a : Fin d) :
    sD h p j - sD h p a =
      fderivWithin ℝ h (affPlane d) p (Pi.single j 1 - Pi.single a 1) := by
  unfold sD
  simp_rw [lineDeriv_eq h p _ hp (sum_single_sub _ _) hd]
  simp only [map_sub]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp only [sub_sub_sub_cancel_right]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (d:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp

lemma coord {d : ℕ} (μ : Fin d → ℝ) (s c : ℝ) (j a i : Fin d) :
    (μ + s • (c • (Pi.single j (1:ℝ) - Pi.single a 1) : Fin d → ℝ)) i =
      μ i + s * c * ((if i = j then 1 else 0) - (if i = a then 1 else 0)) := by
  simp [Pi.single_apply]
  ring

lemma key_est {d : ℕ} [NeZero d] (h : (Fin d → ℝ) → ℝ) (γ K c : ℝ) (hγ : 0 < γ) (hK : 0 ≤ K)
    (μ : Fin d → ℝ) (hμ : μ ∈ simplexInt d) (j a : Fin d) (hc0 : 0 ≤ c) (hca : c ≤ μ a)
    (hcont : ContinuousOn h (stdSimplex ℝ (Fin d)))
    (hdiff : ∀ p ∈ simplexInt d, DifferentiableWithinAt ℝ h (affPlane d) p)
    (hhol : ∀ i, ∀ p ∈ simplexInt d, ∀ q ∈ simplexInt d,
      |sD h p i - sD h q i| ≤ K * ‖p - q‖ ^ γ) :
    |h (μ + c • (Pi.single j 1 - Pi.single a 1)) - h μ - c * (sD h μ j - sD h μ a)|
      ≤ 2 * K * c ^ (1 + γ) := by
  set v : Fin d → ℝ := c • (Pi.single j 1 - Pi.single a 1) with hvdef
  have hv : ∑ i, v i = 0 := by
    simp only [hvdef, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_single_sub, mul_zero]
  obtain ⟨hμpos, hμsum⟩ := hμ
  have hsum : ∀ s : ℝ, ∑ i, (μ + s • v) i = 1 := by
    intro s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hv, hμsum]
    ring
  -- coordinates along the segment
  have hcoord_ge : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ i, (1 - s) * μ i ≤ (μ + s • v) i := by
    intro s hs0 hs1 i
    rw [hvdef, coord]
    have hμi := (hμpos i).le
    by_cases hia : i = a
    · subst hia
      by_cases hij : i = j
      · rw [if_pos hij, if_pos rfl]; nlinarith
      · rw [if_neg hij, if_pos rfl]; nlinarith [mul_le_mul_of_nonneg_left hca hs0]
    · rw [if_neg hia]
      by_cases hij : i = j
      · rw [if_pos hij]; nlinarith [mul_nonneg hs0 hc0]
      · rw [if_neg hij]; nlinarith
  have hin_int : ∀ s : ℝ, 0 ≤ s → s < 1 → μ + s • v ∈ simplexInt d := by
    intro s hs0 hs1
    refine ⟨fun i => ?_, hsum s⟩
    have := hcoord_ge s hs0 hs1.le i
    have : 0 < (1 - s) * μ i := mul_pos (by linarith) (hμpos i)
    linarith
  have hin_std : ∀ s ∈ Set.Icc (0:ℝ) 1, μ + s • v ∈ stdSimplex ℝ (Fin d) := by
    intro s hs
    refine ⟨fun i => ?_, hsum s⟩
    have := hcoord_ge s hs.1 hs.2 i
    have : 0 ≤ (1 - s) * μ i := mul_nonneg (by linarith [hs.2]) (hμpos i).le
    linarith
  set A : ℝ := c * (sD h μ j - sD h μ a) with hA
  let F : ℝ → ℝ := fun s => h (μ + s • v) - s * A
  let F' : ℝ → ℝ := fun s => fderivWithin ℝ h (affPlane d) (μ + s • v) v - A
  have hFc : ContinuousOn F (Set.Icc 0 1) := by
    have hl : Continuous (fun s : ℝ => μ + s • v) := by fun_prop
    exact (hcont.comp hl.continuousOn hin_std).sub (by fun_prop)
  have hFd : ∀ s ∈ Set.Ioo (0:ℝ) 1, HasDerivAt F (F' s) s := by
    intro s hs
    have h1 := line_hasDerivAt h μ v hμsum hv s (hdiff _ (hin_int s hs.1.le hs.2))
    have h2 : HasDerivAt (fun s : ℝ => s * A) A s := by
      simpa using (hasDerivAt_id s).mul_const A
    exact h1.sub h2
  obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope F F' (by norm_num : (0:ℝ) < 1) hFc hFd
  have hF1 : F 1 - F 0 = h (μ + v) - h μ - A := by
    simp [F]; ring
  rw [sub_zero, div_one, hF1] at hslope
  rw [← hslope]
  -- compute F' s
  have hξ := hin_int s hs.1.le hs.2
  have hlin : fderivWithin ℝ h (affPlane d) (μ + s • v) v
      = c * (sD h (μ + s • v) j - sD h (μ + s • v) a) := by
    rw [sD_sub h _ (hsum s) (hdiff _ hξ) j a, hvdef, map_smul, smul_eq_mul]
  simp only [F', hlin, hA]
  have hnorm : ‖(μ + s • v) - μ‖ ≤ c := by
    rw [add_sub_cancel_left]
    refine (pi_norm_le_iff_of_nonneg hc0).2 (fun i => ?_)
    rw [Real.norm_eq_abs]
    have : (s • v) i = s * c * ((if i = j then 1 else 0) - (if i = a then 1 else 0)) := by
      have := coord (0 : Fin d → ℝ) s c j a i
      simpa [hvdef] using this
    rw [this, abs_mul, abs_mul, abs_of_nonneg hs.1.le, abs_of_nonneg hc0]
    have hb : |((if i = j then (1:ℝ) else 0) - (if i = a then 1 else 0))| ≤ 1 := by
      split_ifs <;> norm_num
    have : s * c ≤ c := by nlinarith [hs.2]
    calc s * c * |((if i = j then (1:ℝ) else 0) - (if i = a then 1 else 0))| ≤ s * c * 1 :=
          mul_le_mul_of_nonneg_left hb (by nlinarith [hs.1])
      _ ≤ c := by linarith
  have hpow : ‖(μ + s • v) - μ‖ ^ γ ≤ c ^ γ :=
    Real.rpow_le_rpow (norm_nonneg _) hnorm hγ.le
  have hj := hhol j _ hξ μ ⟨hμpos, hμsum⟩
  have ha := hhol a _ hξ μ ⟨hμpos, hμsum⟩
  have heq : c * (sD h (μ + s • v) j - sD h (μ + s • v) a) - c * (sD h μ j - sD h μ a)
      = c * ((sD h (μ + s • v) j - sD h μ j) - (sD h (μ + s • v) a - sD h μ a)) := by ring
  rw [heq, abs_mul, abs_of_nonneg hc0, Real.rpow_one_add' hc0 (by linarith)]
  have htri := abs_sub ((sD h (μ + s • v) j - sD h μ j)) (sD h (μ + s • v) a - sD h μ a)
  have hKp : K * ‖(μ + s • v) - μ‖ ^ γ ≤ K * c ^ γ := mul_le_mul_of_nonneg_left hpow hK
  calc c * |(sD h (μ + s • v) j - sD h μ j) - (sD h (μ + s • v) a - sD h μ a)|
      ≤ c * (2 * (K * c ^ γ)) := by
        apply mul_le_mul_of_nonneg_left _ hc0; linarith
    _ = 2 * K * (c * c ^ γ) := by ring


lemma empQ_update {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (m : Fin N) (j i : Fin d) :
    empQ (Function.update x m j) y i =
      empQ x y i + y m / N * ((if i = j then 1 else 0) - (if i = x m then 1 else 0)) := by
  unfold empQ
  have hd : ∑ l, (if Function.update x m j l = i then y l else 0)
      - ∑ l, (if x l = i then y l else 0)
      = y m * ((if i = j then 1 else 0) - (if i = x m then 1 else 0)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single m]
    · simp only [Function.update_self]
      by_cases h1 : i = j <;> by_cases h2 : i = x m
      · rw [if_pos h1.symm, if_pos h2.symm, if_pos h1, if_pos h2]; ring
      · rw [if_pos h1.symm, if_neg (Ne.symm h2), if_pos h1, if_neg h2]; ring
      · rw [if_neg (Ne.symm h1), if_pos h2.symm, if_neg h1, if_pos h2]; ring
      · rw [if_neg (Ne.symm h1), if_neg (Ne.symm h2), if_neg h1, if_neg h2]; ring
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  have : ∑ l, (if Function.update x m j l = i then y l else 0) =
      ∑ l, (if x l = i then y l else 0)
        + y m * ((if i = j then 1 else 0) - (if i = x m then 1 else 0)) := by
    linarith
  rw [this]; ring

lemma empMeas_update {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (m : Fin N) (j : Fin d) :
    empMeas (Function.update x m j) y =
      empMeas x y + ((y m : ℝ) / N) • (Pi.single j 1 - Pi.single (x m) 1 : Fin d → ℝ) := by
  funext i
  simp only [empMeas, empQ_update, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Pi.single_apply]
  split_ifs <;> push_cast <;> ring

lemma empMeas_ge {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N) (m : Fin N) :
    (y m : ℝ) / N ≤ empMeas x y (x m) := by
  simp only [empMeas, empQ]
  push_cast
  rw [div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have := Finset.single_le_sum (f := fun l => (if x l = x m then (y l : ℝ) else 0))
    (s := Finset.univ) (fun l _ => by split_ifs <;> simp [hy.1 l]) (Finset.mem_univ m)
  refine le_trans (by simpa using this) (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

lemma empMeas_sum {d N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ)
    (hy : y ∈ Yset N) : ∑ i, empMeas x y i = 1 := by
  have hq : ∑ i, empQ x y i = 1 := by
    unfold empQ
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hy.2]
    have hN' : (N:ℚ) ≠ 0 := by positivity
    field_simp
  simp only [empMeas]
  exact_mod_cast hq

end WFMFG49

open WFMFG49

theorem solution (d : ℕ) [NeZero d] (γ' T : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hT : 0 < T)
    (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (hU : WFReg γ' T U) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∀ (l m : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
      t ∈ Set.Icc 0 T → y ∈ Yset N → (∀ i, 0 < empMeas x y i) → ∀ j : Fin d,
      (m ≠ l →
        |zN U l t (Function.update x m j) y - zN U l t x y
            - ((y m : ℝ) / N)
              * (sD (U (x l) t) (empMeas x y) j - sD (U (x l) t) (empMeas x y) (x m))| ≤
          C * (y m : ℝ) ^ (1 + γ' / 2) / (N : ℝ) ^ (1 + γ' / 2)) ∧
      |zN U l t (Function.update x l j) y - zN U l t x y
          - (U j t (empMeas x y) - U (x l) t (empMeas x y))
          - ((y l : ℝ) / N) * (sD (U j t) (empMeas x y) j - sD (U j t) (empMeas x y) (x l))| ≤
        C * (y l : ℝ) ^ (1 + γ' / 2) / (N : ℝ) ^ (1 + γ' / 2) := by
  obtain ⟨hc, hdiff, K, hK⟩ := hU
  refine ⟨2 * K, ?_⟩
  intro N hN l m t x y ht hy hpos j
  have hμ : empMeas x y ∈ simplexInt d := ⟨hpos, empMeas_sum hN x y hy⟩
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK j j j t ht _ hμ _ hμ).1
  have hγ : 0 < γ' / 2 := by linarith
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  -- generic estimate for the component `i`
  have est : ∀ (i : Fin d) (n : Fin N),
      |U i t (empMeas (Function.update x n j) y) - U i t (empMeas x y)
        - ((y n : ℝ) / N) * (sD (U i t) (empMeas x y) j - sD (U i t) (empMeas x y) (x n))|
        ≤ 2 * K * (y n : ℝ) ^ (1 + γ' / 2) / (N : ℝ) ^ (1 + γ' / 2) := by
    intro i n
    have hyn : (0:ℝ) ≤ y n := by exact_mod_cast hy.1 n
    have hcont : ContinuousOn (U i t) (stdSimplex ℝ (Fin d)) := by
      have := (hc i).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun p hp => (⟨ht, hp⟩ : ((t, p) : ℝ × (Fin d → ℝ)) ∈ Set.Icc 0 T ×ˢ stdSimplex ℝ (Fin d)))
      exact this
    have hE := key_est (U i t) (γ' / 2) K ((y n : ℝ) / N) hγ hK0 (empMeas x y) hμ j (x n)
      (by positivity) (empMeas_ge x y hy n) hcont
      (fun p hp => (hdiff i t ht p hp).1)
      (fun k p hp q hq => (hK i k k t ht p hp q hq).2.2.1)
    rw [empMeas_update, mul_div_assoc]
    rw [Real.div_rpow hyn hNpos.le] at hE
    exact hE
  refine ⟨fun hml => ?_, ?_⟩
  · have := est (x l) m
    simpa [zN, Function.update_of_ne (Ne.symm hml)] using this
  · have := est j l
    have e : zN U l t (Function.update x l j) y - zN U l t x y
          - (U j t (empMeas x y) - U (x l) t (empMeas x y))
        = U j t (empMeas (Function.update x l j) y) - U j t (empMeas x y) := by
      simp [zN]
    rw [e]
    exact this

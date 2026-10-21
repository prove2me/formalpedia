-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:31:18.369832+00:00
-- url     : https://prove2.me/submissions/10be2951-2807-4add-8897-52b8fe533b4f

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model
import Theorems.Thm_RandomLeadGBS_Diffusion_eq_14

open Filter Topology
open RandomLeadGBS.Diffusion

namespace GBSL4

/-- Row sums of the rate matrix against a test function. -/
lemma row (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    (fun s' => rate P r s s' * h s') =
      fun s' => (if s' = afterCustomer P r s then r * h (afterCustomer P r s) else 0) +
        (if s' = afterItem P r s then P.β * (s.2 : ℝ) * h (afterItem P r s) else 0) := by
  funext s'
  simp only [rate, add_mul]
  congr 1
  · split_ifs with h1
    · subst h1; rfl
    · simp
  · by_cases h1 : s' = afterItem P r s
    · subst h1
      by_cases hz : 1 ≤ s.2
      · simp [hz]
      · have : s.2 = 0 := by omega
        simp [this]
    · simp [h1]

lemma row_summable (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    Summable (fun s' => rate P r s s' * h s') := by
  rw [row]
  exact (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all)).add
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all))

lemma row_tsum (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    ∑' s', rate P r s s' * h s' =
      r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s) := by
  rw [row, Summable.tsum_add
    (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all))
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all)),
    tsum_ite_eq, tsum_ite_eq]

lemma rate_nonneg (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (s s' : State) :
    0 ≤ rate P r s s' := by
  unfold rate
  apply add_nonneg
  · split_ifs <;> linarith
  · split_ifs
    · positivity
    · rfl

/-- The flux identity: for a bounded test function `h`, stationarity gives
`E[ r h(after customer) + β Z h(after item) ] = E[(r + β Z) h]`. -/
lemma flux (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (p : State → ℝ)
    (hp : IsStationary P r p) (h : State → ℝ) (B : ℝ) (hh : ∀ s, |h s| ≤ B) :
    ∑' s, p s * (r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s)) =
      ∑' s, p s * exitRate P r s * h s := by
  obtain ⟨hnn, _hsum, _hone, hsumx, hbal⟩ := hp
  -- summability of the double family
  have hG : Summable (fun x : State × State => p x.1 * rate P r x.1 x.2) := by
    refine (summable_prod_of_nonneg (fun x => mul_nonneg (hnn _) (rate_nonneg P r hr hβ _ _))).mpr
      ⟨fun s => ?_, ?_⟩
    · simpa using (row_summable P r s (fun _ => 1)).mul_left (p s)
    · have : (fun s : State => ∑' s' : State, p (s, s').1 * rate P r (s, s').1 (s, s').2) =
          fun s => p s * exitRate P r s := by
        funext s
        simp only
        rw [tsum_mul_left]
        have := row_tsum P r s (fun _ => 1)
        simp only [mul_one] at this
        rw [this, exitRate]
      rw [this]; exact hsumx
  have hF : Summable (Function.uncurry (fun s s' : State => p s * rate P r s s' * h s')) := by
    refine Summable.of_norm_bounded (hG.mul_left B) (fun x => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hnn _), abs_of_nonneg (rate_nonneg P r hr hβ _ _)]
    have := hh x.2
    have h0 : 0 ≤ p x.1 * rate P r x.1 x.2 := mul_nonneg (hnn _) (rate_nonneg P r hr hβ _ _)
    nlinarith
  symm
  calc ∑' s, p s * exitRate P r s * h s
      = ∑' s', (∑' s, p s * rate P r s s') * h s' := by
        congr 1; funext s'; rw [hbal s']
    _ = ∑' s', ∑' s, p s * rate P r s s' * h s' := by
        congr 1; funext s'; rw [tsum_mul_right]
    _ = ∑' s, ∑' s', p s * rate P r s s' * h s' := hF.tsum_comm
    _ = ∑' s, p s * (r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s)) := by
        congr 1; funext s
        rw [← row_tsum, ← tsum_mul_left]
        congr 1; funext s'; ring

lemma orderStep_ge (P : Params) (r : ℝ) (y : ℤ) (z : ℕ) :
    ⌈truncTarget P r y⌉ ≤ ((orderStep P r y z : ℕ) : ℤ) := by
  simp only [orderStep]
  rw [Int.ceil_sub_natCast]
  have h := Int.self_le_toNat (⌈truncTarget P r y⌉ - (z : ℤ))
  push_cast
  omega

/-- A stationary distribution vanishes on states with `Z < ⌈T(Y)⌉` (they are never entered). -/
lemma support (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (p : State → ℝ)
    (hp : IsStationary P r p) (s : State) (hs : ((s.2 : ℕ) : ℤ) < ⌈truncTarget P r s.1⌉) :
    p s = 0 := by
  have hb := hp.2.2.2.2 s
  have h0 : ∀ s0 : State, p s0 * rate P r s0 s = 0 := by
    intro s0
    have : rate P r s0 s = 0 := by
      unfold rate
      rw [if_neg, if_neg]
      · simp
      · rintro ⟨-, h⟩
        have := orderStep_ge P r (s0.1 + 1) (s0.2 - 1)
        rw [h] at hs
        simp only [afterItem] at hs
        omega
      · intro h
        have := orderStep_ge P r (s0.1 - 1) s0.2
        rw [h] at hs
        simp only [afterCustomer] at hs
        omega
    rw [this, mul_zero]
  simp only [h0, tsum_zero] at hb
  have hpos : 0 < exitRate P r s := by
    unfold exitRate; positivity
  rcases mul_eq_zero.mp hb.symm with h | h
  · exact h
  · linarith

lemma os_eq (P : Params) (r : ℝ) (y : ℤ) (z : ℕ) :
    ((orderStep P r y z : ℕ) : ℤ) = max (z : ℤ) ⌈truncTarget P r y⌉ := by
  simp only [orderStep]
  rw [Int.ceil_sub_natCast]
  push_cast
  rcases le_total ⌈truncTarget P r y⌉ (z : ℤ) with h | h
  · rw [Int.toNat_eq_zero.mpr (by omega), max_eq_left h]; simp
  · rw [Int.toNat_of_nonneg (by omega), max_eq_right h]; ring


/-! ### Integer description of the targets (centering `x∗ ≡ 0`) -/

/-- `a(y) = ⌈X∗⌉ − γ y = ⌈X(y)⌉`. -/
noncomputable def aI (P : Params) (r : ℝ) (y : ℤ) : ℤ := ⌈Xstar P r⌉ - (P.γ : ℤ) * y
/-- `m = ⌈X∗ + f⌉`. -/
noncomputable def mI (P : Params) (r : ℝ) : ℤ := ⌈Xstar P r + P.f r⌉

variable {P : Params} {r : ℝ}

lemma target_eq0 (hx : ∀ r, P.xs r = 0) (y : ℤ) :
    target P r y = Xstar P r - (((P.γ : ℤ) * y : ℤ) : ℝ) := by
  simp [target, hx r]

lemma ceil_target (hx : ∀ r, P.xs r = 0) (y : ℤ) : ⌈target P r y⌉ = aI P r y := by
  rw [target_eq0 hx, Int.ceil_sub_intCast]; rfl

lemma ceil_minXM (hx : ∀ r, P.xs r = 0) (y : ℤ) :
    ⌈min (target P r y) (Xstar P r + P.f r)⌉ = min (aI P r y) (mI P r) := by
  rw [Int.ceil_mono.map_min, ceil_target hx]; rfl

lemma ceilT_eq (hx : ∀ r, P.xs r = 0) (y : ℤ) :
    ⌈truncTarget P r y⌉ = max (min (aI P r y) (mI P r)) 0 := by
  unfold truncTarget
  rw [Int.ceil_mono.map_max, ceil_minXM hx, Int.ceil_zero]

lemma W_eq (hM : 0 < Xstar P r + P.f r) (y : ℤ) :
    min (truncTarget P r y) (target P r y) = min (target P r y) (Xstar P r + P.f r) := by
  unfold truncTarget
  rcases le_total 0 (target P r y) with h | h
  · rw [max_eq_left (le_min h hM.le), min_eq_left (min_le_left _ _)]
  · rw [max_eq_right (le_trans (min_le_left _ _) h), min_eq_right h, min_eq_left (by linarith)]

lemma ceilW_eq (hx : ∀ r, P.xs r = 0) (hM : 0 < Xstar P r + P.f r) (y : ℤ) :
    ⌈min (truncTarget P r y) (target P r y)⌉ = min (aI P r y) (mI P r) := by
  rw [W_eq hM, ceil_minXM hx]

lemma aI_dn (y : ℤ) : aI P r (y - 1) = aI P r y + P.γ := by unfold aI; ring
lemma aI_up (y : ℤ) : aI P r (y + 1) = aI P r y - P.γ := by unfold aI; ring

/-- The gap `D̃⁺ = (Z − min(a, m))⁺` as an integer. -/
noncomputable def dd (P : Params) (r : ℝ) (s : State) : ℤ := max ((s.2 : ℤ) - min (aI P r s.1) (mI P r)) 0

lemma dd_cust (hx : ∀ r, P.xs r = 0) (s : State) (hγ : 1 ≤ P.γ)
    (h1 : max (min (aI P r s.1) (mI P r)) 0 ≤ (s.2 : ℤ)) (h2 : (s.2 : ℤ) ≤ mI P r) :
    dd P r (afterCustomer P r s) = max (dd P r s - P.γ) 0 := by
  have e := os_eq P r (s.1 - 1) s.2
  rw [ceilT_eq hx, aI_dn] at e
  unfold dd
  have e1 : (afterCustomer P r s).1 = s.1 - 1 := rfl
  have e2 : (((afterCustomer P r s).2 : ℕ) : ℤ) = ((orderStep P r (s.1 - 1) s.2 : ℕ) : ℤ) := rfl
  rw [e1, e2, e, aI_dn]
  have : (1 : ℤ) ≤ P.γ := by exact_mod_cast hγ
  omega

lemma dd_item (hx : ∀ r, P.xs r = 0) (s : State) (hγ : 1 ≤ P.γ) (hz : 1 ≤ s.2)
    (h1 : max (min (aI P r s.1) (mI P r)) 0 ≤ (s.2 : ℤ)) :
    dd P r (afterItem P r s) ≤ dd P r s + P.γ - 1 := by
  have e := os_eq P r (s.1 + 1) (s.2 - 1)
  rw [ceilT_eq hx, aI_up] at e
  unfold dd
  have e1 : (afterItem P r s).1 = s.1 + 1 := rfl
  have e2 : (((afterItem P r s).2 : ℕ) : ℤ) = ((orderStep P r (s.1 + 1) (s.2 - 1) : ℕ) : ℤ) := rfl
  rw [e1, e2, e, aI_up]
  have : (1 : ℤ) ≤ P.γ := by exact_mod_cast hγ
  have : (((s.2 - 1 : ℕ)) : ℤ) = (s.2 : ℤ) - 1 := by omega
  rw [this]
  omega

lemma dd_nonneg (s : State) : 0 ≤ dd P r s := le_max_right _ _

lemma ceilT_le_m (hx : ∀ r, P.xs r = 0) (hm : 0 ≤ mI P r) (y : ℤ) : ⌈truncTarget P r y⌉ ≤ mI P r := by
  rw [ceilT_eq hx]; omega

lemma aC_snd (s : State) : (((afterCustomer P r s).2 : ℕ) : ℤ) =
    max (s.2 : ℤ) ⌈truncTarget P r (s.1 - 1)⌉ := os_eq P r (s.1 - 1) s.2

lemma aI_snd (s : State) : (((afterItem P r s).2 : ℕ) : ℤ) =
    max ((s.2 - 1 : ℕ) : ℤ) ⌈truncTarget P r (s.1 + 1)⌉ := os_eq P r (s.1 + 1) (s.2 - 1)

/-- A stationary law does not charge states with more than `m` items in transit. -/
lemma zcap (hx : ∀ r, P.xs r = 0) (hr : 0 < r) (hβ : 0 < P.β) (hm : 0 ≤ mI P r)
    (p : State → ℝ) (hp : IsStationary P r p) (s : State) (hs : mI P r < (s.2 : ℤ)) : p s = 0 := by
  have hp' := hp
  obtain ⟨hnn, hps, -, hpx, -⟩ := hp'
  set K : ℕ := s.2 with hK
  have hfl := flux P r hr hβ p hp (fun t => if K ≤ t.2 then 1 else 0) 1
    (fun t => by split_ifs <;> simp)
  have hC : ∀ t : State, (if K ≤ (afterCustomer P r t).2 then (1 : ℝ) else 0) =
      if K ≤ t.2 then 1 else 0 := by
    intro t
    have e := aC_snd (P := P) (r := r) t
    have c := ceilT_le_m hx hm (t.1 - 1)
    have : K ≤ (afterCustomer P r t).2 ↔ K ≤ t.2 := by omega
    simp only [this]
  have hI : ∀ t : State, (if K ≤ (afterItem P r t).2 then (1 : ℝ) else 0) =
      if K + 1 ≤ t.2 then 1 else 0 := by
    intro t
    have e := aI_snd (P := P) (r := r) t
    have c := ceilT_le_m hx hm (t.1 + 1)
    have : K ≤ (afterItem P r t).2 ↔ K + 1 ≤ t.2 := by omega
    simp only [this]
  simp only [hC, hI] at hfl
  have hb : ∀ t : State, |p t * (r * (if K ≤ t.2 then (1 : ℝ) else 0) +
      P.β * (t.2 : ℝ) * (if K + 1 ≤ t.2 then 1 else 0))| ≤ p t * exitRate P r t := by
    intro t
    have h0 : (0 : ℝ) ≤ t.2 := Nat.cast_nonneg _
    rw [abs_of_nonneg (by apply mul_nonneg (hnn t); split_ifs <;> positivity)]
    apply mul_le_mul_of_nonneg_left _ (hnn t)
    unfold exitRate
    split_ifs <;> nlinarith
  have hb2 : ∀ t : State, |p t * exitRate P r t * (if K ≤ t.2 then (1 : ℝ) else 0)| ≤
      p t * exitRate P r t := by
    intro t
    have : 0 ≤ p t * exitRate P r t := mul_nonneg (hnn t) (by unfold exitRate; positivity)
    split_ifs <;> simp [abs_of_nonneg this, this]
  have s1 := Summable.of_norm_bounded hpx (fun t => by rw [Real.norm_eq_abs]; exact hb t)
  have s2 := Summable.of_norm_bounded hpx (fun t => by rw [Real.norm_eq_abs]; exact hb2 t)
  have hdiff : ∑' t : State, (p t * exitRate P r t * (if K ≤ t.2 then (1 : ℝ) else 0) -
      p t * (r * (if K ≤ t.2 then (1 : ℝ) else 0) +
        P.β * (t.2 : ℝ) * (if K + 1 ≤ t.2 then 1 else 0))) = 0 := by
    rw [Summable.tsum_sub s2 s1, hfl, sub_self]
  have hpt : ∀ t : State, p t * exitRate P r t * (if K ≤ t.2 then (1 : ℝ) else 0) -
      p t * (r * (if K ≤ t.2 then (1 : ℝ) else 0) +
        P.β * (t.2 : ℝ) * (if K + 1 ≤ t.2 then 1 else 0)) =
      if t.2 = K then p t * (P.β * (t.2 : ℝ)) else 0 := by
    intro t
    unfold exitRate
    by_cases h1 : t.2 = K
    · rw [if_pos (by omega), if_neg (by omega), if_pos h1]; ring
    · rw [if_neg h1]
      by_cases h2 : K + 1 ≤ t.2
      · rw [if_pos (by omega), if_pos h2]; ring
      · rw [if_neg (by omega), if_neg h2]; ring
  rw [tsum_congr hpt] at hdiff
  have hnn' : ∀ t : State, 0 ≤ (if t.2 = K then p t * (P.β * (t.2 : ℝ)) else 0) := by
    intro t; split_ifs
    · exact mul_nonneg (hnn t) (by positivity)
    · exact le_rfl
  have hsum3 : Summable (fun t : State => if t.2 = K then p t * (P.β * (t.2 : ℝ)) else 0) := by
    rw [← funext hpt]; exact s2.sub s1
  have hs3 := hsum3.hasSum
  rw [hdiff] at hs3
  have := (hasSum_zero_iff_of_nonneg hnn').mp hs3
  have := congrFun this s
  simp only [Pi.zero_apply] at this
  rw [if_pos hK.symm] at this
  have hz : (0 : ℝ) < s.2 := by
    have : (0 : ℤ) < (s.2 : ℤ) := by omega
    exact_mod_cast this
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exfalso; have : 0 < P.β * (s.2 : ℝ) := by positivity
    linarith

/-- Drift of `D̃²` in rate form. -/
lemma drift_alg (r x d γ : ℝ) (hr : 0 < r) (hx : 0 ≤ x) (hd : 0 ≤ d) (hγ : 1 ≤ γ)
    (hcond : x * (4 * γ - 3) ≤ r * (4 * γ - 1)) :
    r * (d - γ) ^ 2 + x * (d + γ - 1) ^ 2 ≤
      (r + x) * (d ^ 2 - (d / 2 - (γ ^ 2 + (γ - 1) ^ 2))) := by
  have k1 : 0 ≤ r * (2 * γ - 1 / 2) - x * (2 * γ - 3 / 2) := by linarith
  have k2 := mul_nonneg hd k1
  have k3 : 0 ≤ r * (γ - 1) ^ 2 + x * γ ^ 2 := by positivity
  nlinarith

end GBSL4

open GBSL4

theorem solution (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, ∀ p : State → ℝ, IsStationary P r p →
      Summable (fun s => p s * gapD P r s) ∧ Summable (fun s => p s * gapDt P r s) ∧
      ∑' s, p s * gapD P r s ≤ ∑' s, p s * gapDt P r s ∧
      ∑' s, p s * gapDt P r s ≤ C := by
  have hP' := hP
  obtain ⟨hβ, hγ, hfpos, hfr, -⟩ := hP'
  have hγr : (1 : ℝ) ≤ P.γ := by exact_mod_cast hγ
  set c₀ : ℝ := (P.γ : ℝ) ^ 2 + ((P.γ : ℝ) - 1) ^ 2 with hc₀
  have hc₀1 : 1 ≤ c₀ := by nlinarith
  refine ⟨4 * c₀, by linarith, ?_⟩
  -- largeness of r
  have hk : 0 < P.β * (4 * (P.γ : ℝ) - 3) := by
    have : (0 : ℝ) < 4 * P.γ - 3 := by linarith
    positivity
  have hT : Tendsto (fun r : ℝ => P.f r / r + r⁻¹) atTop (𝓝 0) := by
    simpa using hfr.add tendsto_inv_atTop_zero
  have hev := (hT.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (P.β * (4 * P.γ - 3))))).and
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp hev
  refine ⟨r₀, fun r hr p hp => ?_⟩
  obtain ⟨hsmall, hr1⟩ := hr₀ r hr
  have hr : 0 < r := lt_of_lt_of_le one_pos hr1
  have hcondr : P.β * (P.f r + 1) * (4 * (P.γ : ℝ) - 3) ≤ 2 * r := by
    have : (P.f r / r + r⁻¹) * (P.β * (4 * P.γ - 3)) < 1 := by
      rwa [lt_div_iff₀ hk] at hsmall
    have e : (P.f r / r + r⁻¹) * (P.β * (4 * P.γ - 3)) * r = P.β * (P.f r + 1) * (4 * P.γ - 3) := by
      field_simp
    nlinarith
  have hM : 0 < Xstar P r + P.f r := by have := hfpos r; unfold Xstar; positivity
  have hm1 : 1 ≤ mI P r := by
    unfold mI; exact Int.one_le_ceil_iff.mpr hM
  have hm0 : 0 ≤ mI P r := by omega
  have hmle : ((mI P r : ℤ) : ℝ) ≤ Xstar P r + P.f r + 1 := (Int.ceil_lt_add_one _).le
  have hp' := hp
  obtain ⟨hnn, hps, hp1, hpx, -⟩ := hp'
  obtain ⟨hsZ, hZ⟩ := eq_14 P hP hx r hr p hp
  have hexit : ∀ s, 0 < exitRate P r s := fun s => by unfold exitRate; positivity
  have hsumexit : ∑' s, p s * exitRate P r s = 2 * r := by
    have : (fun s => p s * exitRate P r s) = fun s => r * p s + P.β * (p s * (s.2 : ℝ)) := by
      funext s; unfold exitRate; ring
    rw [this, Summable.tsum_add (hps.mul_left r) (hsZ.mul_left P.β), tsum_mul_left, tsum_mul_left,
      hp1, hZ]
    ring
  -- support facts
  have S1 : ∀ s, p s ≠ 0 → max (min (aI P r s.1) (mI P r)) 0 ≤ (s.2 : ℤ) := by
    intro s hs
    by_contra h
    push Not at h
    rw [← ceilT_eq hx] at h
    exact hs (support P r hr hβ p hp s h)
  have S2 : ∀ s, p s ≠ 0 → (s.2 : ℤ) ≤ mI P r := by
    intro s hs
    by_contra h
    push Not at h
    exact hs (zcap hx hr hβ hm0 p hp s h)
  -- the Lyapunov function
  set V : State → ℝ := fun s => ((dd P r s : ℤ) : ℝ) ^ 2 with hV
  set g : State → ℝ := fun s => ((dd P r s : ℤ) : ℝ) / 2 - c₀ with hg
  have hd0 : ∀ s, (0 : ℝ) ≤ ((dd P r s : ℤ) : ℝ) := fun s => by exact_mod_cast dd_nonneg s
  have hVg : ∀ s, 0 ≤ V s - g s := fun s => by
    simp only [hV, hg]; nlinarith [sq_nonneg (((dd P r s : ℤ) : ℝ) - 1 / 4)]
  -- pointwise drift
  have hpt : ∀ (N : ℝ), 0 ≤ N → ∀ s, p s * (r * min (V (afterCustomer P r s)) N +
      P.β * (s.2 : ℝ) * min (V (afterItem P r s)) N) ≤
      p s * exitRate P r s * min (V s - g s) N := by
    intro N hN s
    by_cases hps0 : p s = 0
    · rw [hps0]; simp
    have h1 := S1 s hps0
    have h2 := S2 s hps0
    set d : ℝ := ((dd P r s : ℤ) : ℝ) with hd
    have hdd0 := hd0 s
    have hz0 : (0 : ℝ) ≤ s.2 := Nat.cast_nonneg _
    have hxb : P.β * (s.2 : ℝ) * (4 * (P.γ : ℝ) - 3) ≤ r * (4 * (P.γ : ℝ) - 1) := by
      have : (s.2 : ℝ) ≤ ((mI P r : ℤ) : ℝ) := by exact_mod_cast h2
      have hb : P.β * (s.2 : ℝ) ≤ r + P.β * (P.f r + 1) := by
        have := mul_le_mul_of_nonneg_left (le_trans this hmle) hβ.le
        have e : P.β * (Xstar P r + P.f r + 1) = r + P.β * (P.f r + 1) := by
          unfold Xstar; field_simp; ring
        linarith
      have : (0 : ℝ) ≤ 4 * P.γ - 3 := by linarith
      nlinarith
    have hCb : V (afterCustomer P r s) ≤ (d - P.γ) ^ 2 := by
      simp only [hV]
      rw [dd_cust hx s hγ h1 h2]
      push_cast
      rcases le_total ((dd P r s : ℝ) - P.γ) 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg (((dd P r s : ℤ) : ℝ) - P.γ)]
      · rw [max_eq_left h]
    have hIb : P.β * (s.2 : ℝ) * min (V (afterItem P r s)) N ≤
        P.β * (s.2 : ℝ) * (d + P.γ - 1) ^ 2 := by
      rcases Nat.eq_zero_or_pos s.2 with hz | hz
      · rw [hz]; simp
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine le_trans (min_le_left _ _) ?_
        simp only [hV]
        have h3 := dd_item hx s hγ hz h1
        have h4 := dd_nonneg (P := P) (r := r) (afterItem P r s)
        have h5 : ((dd P r (afterItem P r s) : ℤ) : ℝ) ≤ d + P.γ - 1 := by
          have : ((dd P r (afterItem P r s) : ℤ) : ℝ) ≤ ((dd P r s + P.γ - 1 : ℤ) : ℝ) := by
            exact_mod_cast h3
          push_cast at this; exact this
        have h6 : (0 : ℝ) ≤ ((dd P r (afterItem P r s) : ℤ) : ℝ) := by exact_mod_cast h4
        nlinarith
    have hdrift := drift_alg r (P.β * (s.2 : ℝ)) d P.γ hr (by positivity) hdd0 hγr hxb
    have hsum1 : r * min (V (afterCustomer P r s)) N + P.β * (s.2 : ℝ) * min (V (afterItem P r s)) N ≤
        exitRate P r s * (V s - g s) := by
      have := mul_le_mul_of_nonneg_left (le_trans (min_le_left _ N) hCb) hr.le
      unfold exitRate
      simp only [hV, hg, ← hd] at this ⊢
      nlinarith
    have hsum2 : r * min (V (afterCustomer P r s)) N + P.β * (s.2 : ℝ) * min (V (afterItem P r s)) N ≤
        exitRate P r s * N := by
      have := mul_le_mul_of_nonneg_left (min_le_right (V (afterCustomer P r s)) N) hr.le
      have := mul_le_mul_of_nonneg_left (min_le_right (V (afterItem P r s)) N)
        (by positivity : (0 : ℝ) ≤ P.β * s.2)
      unfold exitRate; linarith
    rw [show p s * exitRate P r s * min (V s - g s) N = p s * (exitRate P r s * min (V s - g s) N) by ring]
    apply mul_le_mul_of_nonneg_left _ (hnn s)
    rw [mul_min_of_nonneg _ _ (hexit s).le]
    exact le_min hsum1 hsum2
  -- averaged inequality
  have hmean : ∀ N : ℝ, 0 ≤ N →
      ∑' s, p s * exitRate P r s * (min (V s) N - min (V s - g s) N) ≤ 0 := by
    intro N hN
    have hhb : ∀ s, |min (V s) N| ≤ N := fun s => by
      rw [abs_of_nonneg (le_min (by simp only [hV]; positivity) hN)]; exact min_le_right _ _
    have hfl := flux P r hr hβ p hp (fun s => min (V s) N) N hhb
    have hw0 : ∀ s, 0 ≤ p s * exitRate P r s := fun s => mul_nonneg (hnn s) (hexit s).le
    have sA : Summable (fun s => p s * exitRate P r s * min (V s) N) :=
      Summable.of_nonneg_of_le (fun s => mul_nonneg (hw0 s) (le_min (by simp only [hV]; positivity) hN))
        (fun s => mul_le_mul_of_nonneg_left (min_le_right _ _) (hw0 s)) (hpx.mul_right N)
    have sB : Summable (fun s => p s * exitRate P r s * min (V s - g s) N) :=
      Summable.of_nonneg_of_le (fun s => mul_nonneg (hw0 s) (le_min (hVg s) hN))
        (fun s => mul_le_mul_of_nonneg_left (min_le_right _ _) (hw0 s)) (hpx.mul_right N)
    have sL : Summable (fun s => p s * (r * min (V (afterCustomer P r s)) N +
        P.β * (s.2 : ℝ) * min (V (afterItem P r s)) N)) := by
      refine Summable.of_norm_bounded (hpx.mul_right N) (fun s => ?_)
      have a1 : 0 ≤ min (V (afterCustomer P r s)) N := le_min (by simp only [hV]; positivity) hN
      have a2 : 0 ≤ min (V (afterItem P r s)) N := le_min (by simp only [hV]; positivity) hN
      have a3 := min_le_right (V (afterCustomer P r s)) N
      have a4 := min_le_right (V (afterItem P r s)) N
      have hz0 : (0 : ℝ) ≤ s.2 := Nat.cast_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn s) (by positivity))]
      rw [show p s * exitRate P r s * N = p s * (exitRate P r s * N) by ring]
      apply mul_le_mul_of_nonneg_left _ (hnn s)
      have b1 := mul_le_mul_of_nonneg_left a3 hr.le
      have b2 := mul_le_mul_of_nonneg_left a4 (by positivity : (0 : ℝ) ≤ P.β * s.2)
      unfold exitRate
      linarith
    have hle := Summable.tsum_le_tsum (hpt N hN) sL sB
    rw [hfl] at hle
    rw [show (fun s => p s * exitRate P r s * (min (V s) N - min (V s - g s) N)) =
      fun s => p s * exitRate P r s * min (V s) N - p s * exitRate P r s * min (V s - g s) N from
        funext fun s => by ring, Summable.tsum_sub sA sB]
    linarith
  -- finite partial sums
  have hA : ∀ A : Finset State, ∑ s ∈ A, p s * ((dd P r s : ℤ) : ℝ) ≤ 4 * c₀ := by
    intro A
    set N : ℝ := ∑ s ∈ A, (V s + (V s - g s)) + 1 with hN
    have hNA : ∀ s ∈ A, V s ≤ N ∧ V s - g s ≤ N := by
      intro s hs
      have hle : V s + (V s - g s) ≤ ∑ s ∈ A, (V s + (V s - g s)) :=
        Finset.single_le_sum (f := fun s => V s + (V s - g s))
          (fun i _ => by have := hVg i; simp only [hV] at this ⊢; positivity) hs
      have := hVg s
      have : 0 ≤ V s := by simp only [hV]; positivity
      constructor <;> linarith
    have hN0 : 0 ≤ N := by
      have : 0 ≤ ∑ s ∈ A, (V s + (V s - g s)) :=
        Finset.sum_nonneg (fun i _ => by have := hVg i; simp only [hV] at this ⊢; positivity)
      linarith
    have hw0 : ∀ s, 0 ≤ p s * exitRate P r s := fun s => mul_nonneg (hnn s) (hexit s).le
    have hH0 : ∀ s, 0 ≤ min (V s) N - min (V s - g s) N + c₀ := by
      intro s
      have hgl : -c₀ ≤ g s := by simp only [hg]; linarith [hd0 s]
      by_cases hgs : 0 ≤ g s
      · have : min (V s - g s) N ≤ min (V s) N := min_le_min (by linarith) le_rfl
        linarith
      · push Not at hgs
        have : min (V s - g s) N ≤ min (V s) N - g s := by
          rcases le_total (V s) N with h1 | h1
          · rw [min_eq_left h1]; exact min_le_left _ _
          · rw [min_eq_right h1]; linarith [min_le_right (V s - g s) N]
        linarith
    have sH : Summable (fun s => p s * exitRate P r s * (min (V s) N - min (V s - g s) N + c₀)) := by
      refine Summable.of_norm_bounded (hpx.mul_right (N + c₀)) (fun s => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 s) (hH0 s))]
      apply mul_le_mul_of_nonneg_left _ (hw0 s)
      have := le_min (hVg s) hN0
      have := min_le_right (V s) N
      linarith
    have hsumH : ∑' s, p s * exitRate P r s * (min (V s) N - min (V s - g s) N + c₀) ≤ 2 * r * c₀ := by
      have sM : Summable (fun s => p s * exitRate P r s * (min (V s) N - min (V s - g s) N)) := by
        have := sH.sub (hpx.mul_right c₀)
        refine this.congr (fun s => by ring)
      rw [show (fun s => p s * exitRate P r s * (min (V s) N - min (V s - g s) N + c₀)) =
        fun s => p s * exitRate P r s * (min (V s) N - min (V s - g s) N) + p s * exitRate P r s * c₀
        from funext fun s => by ring, Summable.tsum_add sM (hpx.mul_right c₀), tsum_mul_right,
        hsumexit]
      linarith [hmean N hN0]
    have hfin := sH.sum_le_tsum A (fun s _ => mul_nonneg (hw0 s) (hH0 s))
    have hAeq : ∀ s ∈ A, p s * exitRate P r s * (min (V s) N - min (V s - g s) N + c₀) =
        p s * exitRate P r s * (((dd P r s : ℤ) : ℝ) / 2) := by
      intro s hs
      obtain ⟨a1, a2⟩ := hNA s hs
      rw [min_eq_left a1, min_eq_left a2]
      simp only [hg]; ring
    rw [Finset.sum_congr rfl hAeq] at hfin
    have hlow : ∀ s, r * (p s * ((dd P r s : ℤ) : ℝ)) / 2 ≤
        p s * exitRate P r s * (((dd P r s : ℤ) : ℝ) / 2) := by
      intro s
      have : r ≤ exitRate P r s := by
        unfold exitRate; exact le_add_of_nonneg_right (by positivity)
      have := mul_le_mul_of_nonneg_right this (mul_nonneg (hnn s) (hd0 s))
      linarith
    have hsum_low := Finset.sum_le_sum (fun s (_ : s ∈ A) => hlow s)
    rw [← Finset.sum_div, ← Finset.mul_sum] at hsum_low
    have : r * ∑ s ∈ A, p s * ((dd P r s : ℤ) : ℝ) ≤ r * (4 * c₀) := by
      linarith [hsum_low, hfin, hsumH]
    exact le_of_mul_le_mul_left this hr
  have hdd_nn : ∀ s, 0 ≤ p s * ((dd P r s : ℤ) : ℝ) := fun s => mul_nonneg (hnn s) (hd0 s)
  have hsdd : Summable (fun s => p s * ((dd P r s : ℤ) : ℝ)) := summable_of_sum_le hdd_nn hA
  have hdd_le : ∑' s, p s * ((dd P r s : ℤ) : ℝ) ≤ 4 * c₀ := Real.tsum_le_of_sum_le hdd_nn hA
  -- identify the gaps
  have hDt : ∀ s, p s * gapDt P r s = p s * ((dd P r s : ℤ) : ℝ) := by
    intro s
    by_cases hps0 : p s = 0
    · rw [hps0]; simp
    congr 1
    have h1 := S1 s hps0
    unfold gapDt dd
    rw [ceilW_eq hx hM, max_eq_left (by omega)]
    push_cast; ring
  have hD : ∀ s, 0 ≤ p s * gapD P r s ∧ p s * gapD P r s ≤ p s * gapDt P r s := by
    intro s
    by_cases hps0 : p s = 0
    · rw [hps0]; simp
    have h1 := S1 s hps0
    unfold gapD gapDt
    rw [ceilT_eq hx, ceilW_eq hx hM]
    have a1 : (((max (min (aI P r s.1) (mI P r)) 0 : ℤ)) : ℝ) ≤ (s.2 : ℝ) := by exact_mod_cast h1
    have a2 : (((min (aI P r s.1) (mI P r) : ℤ)) : ℝ) ≤ ((max (min (aI P r s.1) (mI P r)) 0 : ℤ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    constructor
    · apply mul_nonneg (hnn s); linarith
    · apply mul_le_mul_of_nonneg_left _ (hnn s); linarith
  have hsDt : Summable (fun s => p s * gapDt P r s) := by
    rw [funext hDt]; exact hsdd
  have hsD : Summable (fun s => p s * gapD P r s) :=
    Summable.of_nonneg_of_le (fun s => (hD s).1) (fun s => (hD s).2) hsDt
  refine ⟨hsD, hsDt, Summable.tsum_le_tsum (fun s => (hD s).2) hsD hsDt, ?_⟩
  rw [funext hDt]; exact hdd_le

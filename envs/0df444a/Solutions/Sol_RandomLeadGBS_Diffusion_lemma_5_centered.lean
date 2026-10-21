-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.lemma_5_centered
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:28:47.350987+00:00
-- url     : https://prove2.me/submissions/806b20ee-9a6c-49ca-b04d-33dc1a00c8aa

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

-- ===== part L5a =====

open Filter Topology
open RandomLeadGBS.Diffusion

namespace GBSL5

/-- Cut equations for the artificial chain: `β Ẑ(j) q(j) = r q(j+1)`. -/
lemma art_cut (P : Params) (r : ℝ) (hβ : 0 < P.β) (p : ℤ → ℝ) (hp : IsArtStationary P r p) :
    ∀ j : ℤ, p j * (P.β * (artZ P r j : ℝ)) = p (j + 1) * r := by
  obtain ⟨_hnn, hsum, hone, hsumx, hbal⟩ := hp
  set Z : ℤ → ℝ := fun j => (artZ P r j : ℝ) with hZ
  -- a j : up-flux, b j : down-flux
  set a : ℤ → ℝ := fun j => p j * (P.β * Z j) with ha
  set b : ℤ → ℝ := fun j => p j * r with hb
  have hsa : Summable a := by
    have : a = fun j => p j * artExitRate P r j - p j * r := by
      funext j; simp only [ha, artExitRate, hZ]; ring
    rw [this]; exact hsumx.sub (hsum.mul_right r)
  have hsZ : Summable (fun j : ℤ => p j * Z j) := by
    have : (fun j : ℤ => p j * Z j) = fun j => a j / P.β := by
      funext j; simp only [ha]; field_simp
    rw [this]; exact hsa.div_const _
  -- balance equation in flux form
  have hbal' : ∀ j' : ℤ, b (j' + 1) + a (j' - 1) = b j' + a j' := by
    intro j'
    have h := hbal j'
    have hfun : (fun j => p j * artRate P r j j') =
        fun j => (if j = j' + 1 then b (j' + 1) else 0) + (if j = j' - 1 then a (j' - 1) else 0) := by
      funext j
      simp only [artRate, mul_add]
      congr 1
      · by_cases h1 : j = j' + 1
        · subst h1; simp [hb]
        · have : ¬ j' = j - 1 := by omega
          simp [h1, this]
      · by_cases h1 : j = j' - 1
        · subst h1; simp [ha, hZ]
        · have : ¬ j' = j + 1 := by omega
          simp [h1, this]
    rw [hfun, Summable.tsum_add (summable_of_ne_finset_zero (s := {j' + 1}) (by intro j hj; simp_all))
      (summable_of_ne_finset_zero (s := {j' - 1}) (by intro j hj; simp_all)),
      tsum_ite_eq, tsum_ite_eq] at h
    rw [h]; simp only [ha, hb, artExitRate, hZ]; ring
  -- φ j = a j - b (j+1) is constant
  set φ : ℤ → ℝ := fun j => a j - b (j + 1) with hφ
  have hstep : ∀ j : ℤ, φ j = φ (j - 1) := by
    intro j
    have := hbal' j
    simp only [hφ, sub_add_cancel]; linarith
  have hconst : ∀ j : ℤ, φ j = φ 0 := by
    intro j
    induction j using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [hstep (k + 1)]; simpa using ih
    | pred k ih => have := hstep (-(k:ℤ)); linarith
  have hsb1 : Summable (fun j : ℤ => b (j + 1)) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr (hsum.mul_right r)
  have hsφ : Summable φ := hsa.sub hsb1
  have hφ0 : φ 0 = 0 := by
    have : Summable (fun _ : ℤ => φ 0) := by
      have : φ = fun _ => φ 0 := funext hconst
      rwa [this] at hsφ
    exact (summable_const_iff (φ 0)).mp this
  have hab : ∀ j, a j = b (j + 1) := by
    intro j; have := hconst j; rw [hφ0] at this; simp only [hφ] at this; linarith
  exact hab


/-- `a(y) = ⌈X∗ + γ x∗⌉ − γ y`. -/
noncomputable def aI (P : Params) (r : ℝ) (y : ℤ) : ℤ := ⌈Xstar P r + (P.γ : ℝ) * P.xs r⌉ - (P.γ : ℤ) * y
noncomputable def mI (P : Params) (r : ℝ) : ℤ := ⌈Xstar P r + P.f r⌉

lemma target_eq0 (P : Params) (r : ℝ) (y : ℤ) :
    target P r y = (Xstar P r + (P.γ : ℝ) * P.xs r) - (((P.γ : ℤ) * y : ℤ) : ℝ) := by
  simp [target]; ring

lemma ceilT_eq (P : Params) (r : ℝ) (y : ℤ) :
    ⌈truncTarget P r y⌉ = max (min (aI P r y) (mI P r)) 0 := by
  unfold truncTarget
  rw [Int.ceil_mono.map_max, Int.ceil_mono.map_min, target_eq0, Int.ceil_sub_intCast, Int.ceil_zero]
  rfl

lemma artZ_int (P : Params) (r : ℝ) (y : ℤ) :
    ((artZ P r y : ℕ) : ℤ) = max (min (aI P r y) (mI P r)) 0 := by
  unfold artZ
  rw [Int.natCast_ceil_eq_ceil (show 0 ≤ truncTarget P r y from le_max_right _ _), ceilT_eq]

/-- Ratio `q(j+1)/q(j) = β Ẑ(j)/r`. -/
noncomputable def aa (P : Params) (r : ℝ) (j : ℤ) : ℝ := P.β * (artZ P r j : ℝ) / r
noncomputable def kk (P : Params) (r : ℝ) : ℤ := ⌊P.xs r⌋
noncomputable def ist (P : Params) (r : ℝ) : ℝ := (((aI P r 0 : ℤ) : ℝ) - Xstar P r) / P.γ
noncomputable def rho (P : Params) (r : ℝ) : ℝ := P.β * P.γ / r

variable {P : Params} {r : ℝ}

lemma aa_nonneg (hP : P.Standing) (hr : 0 < r) (j : ℤ) : 0 ≤ aa P r j := by
  unfold aa; have := hP.1; positivity

lemma artZ_real (P : Params) (r : ℝ) (y : ℤ) :
    (artZ P r y : ℝ) = (((max (min (aI P r y) (mI P r)) 0 : ℤ)) : ℝ) := by
  rw [← artZ_int]; rfl

lemma lin_id (hP : P.Standing) (hr : 0 < r) (j : ℤ) :
    P.β * (((aI P r j : ℤ)) : ℝ) / r = 1 - rho P r * ((j : ℝ) - ist P r) := by
  have hβ := hP.1
  have hγ1 : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have hγ : (0 : ℝ) < P.γ := by linarith
  have e0 : (((aI P r 0 : ℤ)) : ℝ) = ((⌈Xstar P r + (P.γ : ℝ) * P.xs r⌉ : ℤ) : ℝ) := by
    unfold aI; simp
  unfold rho ist
  rw [e0]
  unfold aI
  push_cast
  unfold Xstar
  field_simp
  ring

lemma aa_up (hP : P.Standing) (hr : 0 < r) (j : ℤ) (h : aI P r j ≤ mI P r) :
    aa P r j = max (1 - rho P r * ((j : ℝ) - ist P r)) 0 := by
  have hβ := hP.1
  unfold aa
  rw [artZ_real, min_eq_left h]
  rw [← lin_id hP hr j]
  rcases le_total 0 (aI P r j) with h0 | h0
  · rw [max_eq_left h0, max_eq_left (by positivity)]
  · rw [max_eq_right h0]
    have : (((aI P r j : ℤ)) : ℝ) ≤ 0 := by exact_mod_cast h0
    have : P.β * (((aI P r j : ℤ)) : ℝ) / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hβ.le this) hr.le
    rw [max_eq_right this]; simp

lemma aa_dn (hP : P.Standing) (hr : 0 < r) (j : ℤ) (h : 0 ≤ aI P r j) :
    aa P r j = min (1 - rho P r * ((j : ℝ) - ist P r)) (P.β * ((mI P r : ℤ) : ℝ) / r) := by
  have hβ := hP.1
  unfold aa
  rw [artZ_real, ← lin_id hP hr j]
  have hm : 0 ≤ mI P r := by
    unfold mI; have := hP.2.2.1 r; apply Int.ceil_nonneg; unfold Xstar; positivity
  rw [max_eq_left (le_min h hm)]
  rcases le_total (aI P r j) (mI P r) with h1 | h1
  · rw [min_eq_left h1, min_eq_left]
    have : (((aI P r j : ℤ)) : ℝ) ≤ ((mI P r : ℤ) : ℝ) := by exact_mod_cast h1
    apply div_le_div_of_nonneg_right _ hr.le
    exact mul_le_mul_of_nonneg_left this hβ.le
  · rw [min_eq_right h1, min_eq_right]
    have : ((mI P r : ℤ) : ℝ) ≤ (((aI P r j : ℤ)) : ℝ) := by exact_mod_cast h1
    apply div_le_div_of_nonneg_right _ hr.le
    exact mul_le_mul_of_nonneg_left this hβ.le

lemma ist_bounds (hP : P.Standing) :
    P.xs r ≤ ist P r ∧ ist P r < P.xs r + 1 := by
  have hγ1 : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have hγ : (0 : ℝ) < P.γ := by linarith
  have h1 := Int.le_ceil (Xstar P r + (P.γ : ℝ) * P.xs r)
  have h2 := Int.ceil_lt_add_one (Xstar P r + (P.γ : ℝ) * P.xs r)
  have e : (((aI P r 0 : ℤ)) : ℝ) = ((⌈Xstar P r + (P.γ : ℝ) * P.xs r⌉ : ℤ) : ℝ) := by
    unfold aI; simp
  unfold ist
  rw [e]
  constructor
  · rw [le_div_iff₀ hγ]; linarith
  · rw [div_lt_iff₀ hγ]; nlinarith

lemma kk_bounds (hP : P.Standing) :
    ((kk P r : ℤ) : ℝ) ≤ ist P r ∧ ist P r < (kk P r : ℝ) + 2 := by
  have := ist_bounds (r := r) hP
  have h1 := Int.floor_le (P.xs r)
  have h2 := Int.lt_floor_add_one (P.xs r)
  unfold kk
  constructor <;> linarith

/-- Above the reference index the cap is not active (for `f ≥ γ + 1`). -/
lemma aI_le_m (hP : P.Standing) (hr : 0 < r) (hf : (P.γ : ℝ) + 1 ≤ P.f r) (j : ℤ)
    (hj : kk P r ≤ j) : aI P r j ≤ mI P r := by
  have hγ1 : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have h1 := Int.ceil_lt_add_one (Xstar P r + (P.γ : ℝ) * P.xs r)
  have h2 := Int.le_ceil (Xstar P r + P.f r)
  have h3 := Int.floor_le (P.xs r)
  have h4 := Int.lt_floor_add_one (P.xs r)
  have hj' : ((kk P r : ℤ) : ℝ) ≤ j := by exact_mod_cast hj
  unfold kk at hj'
  have : (((aI P r j : ℤ)) : ℝ) < ((mI P r : ℤ) : ℝ) + 1 := by
    unfold aI mI; push_cast
    nlinarith
  have : aI P r j < mI P r + 1 := by exact_mod_cast this
  omega

lemma aI_low_nonneg (hP : P.Standing) (hr : 0 < r) (j : ℤ) (hj : j ≤ kk P r - 1) :
    0 ≤ aI P r j := by
  have hγ1 : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have h1 := Int.le_ceil (Xstar P r + (P.γ : ℝ) * P.xs r)
  have h3 := Int.floor_le (P.xs r)
  have hj' : (j : ℝ) ≤ ((kk P r : ℤ) : ℝ) - 1 := by
    have : ((j : ℤ) : ℝ) ≤ ((kk P r - 1 : ℤ) : ℝ) := by exact_mod_cast hj
    push_cast at this; exact this
  unfold kk at hj'
  have hX : 0 < Xstar P r := by unfold Xstar; have := hP.1; positivity
  have : (0 : ℝ) ≤ (((aI P r j : ℤ)) : ℝ) := by
    unfold aI; push_cast
    nlinarith
  exact_mod_cast this

lemma bm_ge (hP : P.Standing) (hr : 0 < r) :
    1 + P.β * P.f r / r ≤ P.β * ((mI P r : ℤ) : ℝ) / r := by
  have hβ := hP.1
  have h := Int.le_ceil (Xstar P r + P.f r)
  have e : P.β * (Xstar P r + P.f r) / r = 1 + P.β * P.f r / r := by
    unfold Xstar; field_simp
  rw [← e]
  apply div_le_div_of_nonneg_right _ hr.le
  exact mul_le_mul_of_nonneg_left h hβ.le

lemma rho_pos (hP : P.Standing) (hr : 0 < r) : 0 < rho P r := by
  unfold rho; have := hP.1; have : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  positivity

lemma rec (hP : P.Standing) (hr : 0 < r) (q : ℤ → ℝ) (hq : IsArtStationary P r q) (j : ℤ) :
    q (j + 1) = aa P r j * q j := by
  have := art_cut P r hP.1 q hq j
  unfold aa
  field_simp
  linarith

lemma aa_low_ge_one (hP : P.Standing) (hr : 0 < r) (j : ℤ) (hj : j ≤ kk P r - 1) :
    1 ≤ aa P r j := by
  rw [aa_dn hP hr j (aI_low_nonneg hP hr j hj)]
  have hk := (kk_bounds (r := r) hP).1
  have hj' : (j : ℝ) ≤ ((kk P r : ℤ) : ℝ) - 1 := by
    have : ((j : ℤ) : ℝ) ≤ ((kk P r - 1 : ℤ) : ℝ) := by exact_mod_cast hj
    push_cast at this; exact this
  have hρ := rho_pos hP hr
  have hb := bm_ge hP hr
  have : 0 ≤ P.β * P.f r / r := by have := hP.1; have := hP.2.2.1 r; positivity
  apply le_min
  · nlinarith
  · linarith

lemma prod_up (hP : P.Standing) (hr : 0 < r) (q : ℤ → ℝ) (hq : IsArtStationary P r q) (n : ℕ) :
    q (kk P r + n) = q (kk P r) * ∏ t ∈ Finset.range n, aa P r (kk P r + t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
    push_cast
    rw [← add_assoc, rec hP hr q hq]; ring

lemma prod_dn (hP : P.Standing) (hr : 0 < r) (q : ℤ → ℝ) (hq : IsArtStationary P r q) (n : ℕ) :
    q (kk P r - n) * ∏ t ∈ Finset.range n, aa P r (kk P r - 1 - t) = q (kk P r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    have := rec hP hr q hq (kk P r - (n + 1 : ℕ))
    push_cast at this ⊢
    rw [show kk P r - (n + 1) + 1 = kk P r - n by ring] at this
    rw [this, show kk P r - 1 - (n : ℤ) = kk P r - (n + 1) by ring]
    ring

lemma prod_dn_pos (hP : P.Standing) (hr : 0 < r) (n : ℕ) :
    1 ≤ ∏ t ∈ Finset.range n, aa P r (kk P r - 1 - t) := by
  apply Finset.one_le_prod
  intro t _
  exact aa_low_ge_one hP hr _ (by omega)

lemma qk_pos (hP : P.Standing) (hr : 0 < r) (q : ℤ → ℝ) (hq : IsArtStationary P r q) :
    0 < q (kk P r) := by
  have hq' := hq
  obtain ⟨q0, qs, q1, -⟩ := hq'
  by_contra hcon
  have h0 : q (kk P r) = 0 := le_antisymm (not_lt.mp hcon) (q0 _)
  have hall : ∀ j, q j = 0 := by
    intro j
    rcases le_total (kk P r) j with h | h
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = kk P r + n := ⟨(j - kk P r).toNat, by omega⟩
      rw [hn, prod_up hP hr q hq, h0, zero_mul]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = kk P r - n := ⟨(kk P r - j).toNat, by omega⟩
      have := prod_dn hP hr q hq n
      have hp := prod_dn_pos hP hr n
      rw [h0, ← hn] at this
      rcases mul_eq_zero.mp this with h1 | h1
      · exact h1
      · linarith
  simp [hall] at q1

end GBSL5

-- ===== part L5b =====

open Filter Topology
open RandomLeadGBS.Diffusion

namespace GBSL5

lemma sum_lin (n : ℕ) (a b : ℝ) :
    ∑ t ∈ Finset.range n, (a * (t : ℝ) + b) = a * ((n : ℝ) * ((n : ℝ) - 1) / 2) + b * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma log_bound (x : ℝ) (h : |x| ≤ 1 / 2) : |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have h1 : |x| < 1 := by linarith
  have := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one] at this
  rw [add_comm] at this
  refine le_trans this ?_
  rw [div_le_iff₀ (by linarith)]
  have e : |x| ^ (1 + 1) = x ^ 2 := by rw [show 1 + 1 = 2 from rfl, sq_abs]
  rw [e]
  nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * |x|)]

lemma exp_half_le (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1) : Real.exp (z / 2) ≤ 1 + z := by
  rcases h0.lt_or_eq with h | h
  · have := Real.exp_bound_div_one_sub_of_interval' (x := z / 2) (by linarith) (by linarith)
    refine le_trans this.le ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · rw [← h]; simp

variable {P : Params} {r : ℝ}

/-- Upper-side domination: `∏_{t<n} a(k+t) ≤ exp(βγ/2 − βγ n/(2√r))`. -/
lemma up_dom (hP : P.Standing) (hr : 25 ≤ r) (hf : (P.γ : ℝ) + 1 ≤ P.f r) (n : ℕ) :
    ∏ t ∈ Finset.range n, aa P r (kk P r + t) ≤
      Real.exp (P.β * P.γ / 2 - P.β * P.γ * n / (2 * Real.sqrt r)) := by
  have hr0 : 0 < r := by linarith
  have hβγ : 0 < P.β * P.γ := by
    have := hP.1; have : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
    positivity
  have hk := kk_bounds (r := r) hP
  have hρ := rho_pos hP hr0
  -- termwise bound by exponentials
  have hterm : ∀ t ∈ Finset.range n, aa P r (kk P r + t) ≤
      Real.exp (-(rho P r * ((t : ℝ) - 2))) := by
    intro t _
    rw [aa_up hP hr0 _ (aI_le_m hP hr0 hf _ (by omega))]
    apply max_le
    · have h1 := Real.add_one_le_exp (-(rho P r * (((kk P r + t : ℤ) : ℝ) - ist P r)))
      have h2 : -(rho P r * (((kk P r + t : ℤ) : ℝ) - ist P r)) ≤ -(rho P r * ((t : ℝ) - 2)) := by
        push_cast
        have : ((t : ℝ) - 2) ≤ ((kk P r : ℝ) + t - ist P r) := by linarith
        nlinarith
      have h3 := Real.exp_le_exp.mpr h2
      linarith
    · positivity
  calc ∏ t ∈ Finset.range n, aa P r (kk P r + t)
      ≤ ∏ t ∈ Finset.range n, Real.exp (-(rho P r * ((t : ℝ) - 2))) :=
        Finset.prod_le_prod (fun t _ => aa_nonneg hP hr0 _) hterm
    _ = Real.exp (∑ t ∈ Finset.range n, -(rho P r * ((t : ℝ) - 2))) := (Real.exp_sum _ _).symm
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have e : ∑ t ∈ Finset.range n, -(rho P r * ((t : ℝ) - 2)) =
            ∑ t ∈ Finset.range n, (-(rho P r) * (t : ℝ) + 2 * rho P r) :=
          Finset.sum_congr rfl (fun t _ => by ring)
        rw [e, sum_lin]
        have hs : 5 ≤ Real.sqrt r := by
          rw [show (5 : ℝ) = Real.sqrt 25 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt hr
        have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
        have hρe : rho P r = P.β * P.γ / r := rfl
        rw [hρe]
        set s := Real.sqrt r
        have hspos : 0 < s := by linarith
        have key : (n : ℝ) ^ 2 - (5 + s) * n + s ^ 2 ≥ 0 := by
          nlinarith [sq_nonneg ((n : ℝ) - (5 + s) / 2)]
        rw [← hsq]
        have e2 : P.β * P.γ / 2 - P.β * P.γ * n / (2 * s) -
            (-(P.β * P.γ / s ^ 2) * ((n : ℝ) * ((n : ℝ) - 1) / 2) + 2 * (P.β * P.γ / s ^ 2) * n) =
            P.β * P.γ / (2 * s ^ 2) * ((n : ℝ) ^ 2 - (5 + s) * n + s ^ 2) := by
          field_simp; ring
        have : 0 ≤ P.β * P.γ / (2 * s ^ 2) * ((n : ℝ) ^ 2 - (5 + s) * n + s ^ 2) :=
          mul_nonneg (by positivity) key
        linarith

lemma sum_min_ge (s : ℝ) (hs : 0 ≤ s) (m : ℕ) :
    s * ((m : ℝ) - s - 1) ≤ ∑ t ∈ Finset.range m, min ((t : ℝ) + 1) s ∧
      0 ≤ ∑ t ∈ Finset.range m, min ((t : ℝ) + 1) s := by
  induction m with
  | zero => simp; nlinarith
  | succ m ih =>
    rw [Finset.sum_range_succ]
    obtain ⟨h1, h2⟩ := ih
    have h3 : 0 ≤ min ((m : ℝ) + 1) s := le_min (by positivity) hs
    push_cast
    constructor
    · rcases le_total ((m : ℝ) + 1) s with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    · linarith

/-- Lower-side domination: `1/∏_{t<m} a(k−1−t) ≤ exp(βγ − βγ m/(2√r))`. -/
lemma dn_dom (hP : P.Standing) (hr : 1 ≤ r) (hf : (P.γ : ℝ) * Real.sqrt r ≤ P.f r)
    (hf1 : P.β * P.f r / r ≤ 1) (m : ℕ) :
    1 / ∏ t ∈ Finset.range m, aa P r (kk P r - 1 - t) ≤
      Real.exp (P.β * P.γ - P.β * P.γ * m / (2 * Real.sqrt r)) := by
  have hr0 : 0 < r := by linarith
  have hβ := hP.1
  have hγ1 : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have hβγ : 0 < P.β * P.γ := by positivity
  have hk := kk_bounds (r := r) hP
  have hρ := rho_pos hP hr0
  set s := Real.sqrt r with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hr
  have hsq : s ^ 2 = r := Real.sq_sqrt hr0.le
  have hD : rho P r * s ≤ P.β * P.f r / r := by
    unfold rho
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr0]
    nlinarith
  have hterm : ∀ t ∈ Finset.range m,
      Real.exp (rho P r * min ((t : ℝ) + 1) s / 2) ≤ aa P r (kk P r - 1 - t) := by
    intro t _
    have hj : kk P r - 1 - (t : ℤ) ≤ kk P r - 1 := by omega
    rw [aa_dn hP hr0 _ (aI_low_nonneg hP hr0 _ hj)]
    have hz0 : 0 ≤ rho P r * min ((t : ℝ) + 1) s := mul_nonneg hρ.le (le_min (by positivity) (by linarith))
    have hz1 : rho P r * min ((t : ℝ) + 1) s ≤ P.β * P.f r / r :=
      le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hρ.le) hD
    have he := exp_half_le _ hz0 (le_trans hz1 hf1)
    apply le_min
    · have : rho P r * min ((t : ℝ) + 1) s ≤ -(rho P r * ((((kk P r - 1 - t : ℤ)) : ℝ) - ist P r)) := by
        push_cast
        have : min ((t : ℝ) + 1) s ≤ (t : ℝ) + 1 := min_le_left _ _
        have : (t : ℝ) + 1 ≤ ist P r - ((kk P r : ℝ) - 1 - t) := by linarith
        nlinarith
      linarith
    · have := bm_ge hP hr0
      linarith
  have hprod : Real.exp (∑ t ∈ Finset.range m, rho P r * min ((t : ℝ) + 1) s / 2) ≤
      ∏ t ∈ Finset.range m, aa P r (kk P r - 1 - t) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun t _ => (Real.exp_pos _).le) hterm
  have hsum : P.β * P.γ * m / (2 * s) - P.β * P.γ ≤
      ∑ t ∈ Finset.range m, rho P r * min ((t : ℝ) + 1) s / 2 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have h1 := (sum_min_ge s (by linarith) m).1
    have h2 := mul_le_mul_of_nonneg_left h1 hρ.le
    have e : rho P r * (s * ((m : ℝ) - s - 1)) / 2 = P.β * P.γ * m / (2 * s) - P.β * P.γ / 2 -
        P.β * P.γ / (2 * s) := by
      unfold rho; rw [← hsq]; field_simp
    have : P.β * P.γ / (2 * s) ≤ P.β * P.γ / 2 := by
      apply div_le_div_of_nonneg_left hβγ.le (by norm_num); linarith
    linarith
  have hpos : 0 < ∏ t ∈ Finset.range m, aa P r (kk P r - 1 - t) :=
    lt_of_lt_of_le (Real.exp_pos _) hprod
  rw [div_le_iff₀ hpos]
  calc (1 : ℝ) = Real.exp (P.β * P.γ - P.β * P.γ * m / (2 * s)) *
        Real.exp (P.β * P.γ * m / (2 * s) - P.β * P.γ) := by
        rw [← Real.exp_add]; simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact le_trans (Real.exp_le_exp.mpr hsum) hprod

end GBSL5

-- ===== part L5c =====

open Filter Topology
open RandomLeadGBS.Diffusion

namespace GBSL5

variable {P : Params} {r : ℝ}

noncomputable def Jr (P : Params) (r u : ℝ) : ℤ := ⌊P.xs r + u * Real.sqrt r⌋

lemma n_bounds (P : Params) (r u : ℝ) :
    u * Real.sqrt r - 1 < (((Jr P r u - kk P r : ℤ)) : ℝ) ∧
      (((Jr P r u - kk P r : ℤ)) : ℝ) < u * Real.sqrt r + 1 := by
  have h1 := Int.floor_le (P.xs r + u * Real.sqrt r)
  have h2 := Int.lt_floor_add_one (P.xs r + u * Real.sqrt r)
  have h3 := Int.floor_le (P.xs r)
  have h4 := Int.lt_floor_add_one (P.xs r)
  unfold Jr kk
  push_cast
  constructor <;> linarith

/-- The good range of `r`. -/
def Good (P : Params) (r : ℝ) : Prop :=
  25 ≤ r ∧ (P.γ : ℝ) * Real.sqrt r ≤ P.f r ∧ P.β * P.f r / r ≤ 1

lemma good_ev (hP : P.Standing) : ∀ᶠ r in atTop, Good P r := by
  obtain ⟨hβ, hγ, -, hfr, hfs⟩ := hP
  have h1 : ∀ᶠ r in atTop, (P.γ : ℝ) ≤ P.f r / Real.sqrt r := hfs.eventually (eventually_ge_atTop _)
  have h2 : ∀ᶠ r in atTop, P.f r / r < 1 / P.β := hfr.eventually (gt_mem_nhds (by positivity))
  filter_upwards [h1, h2, eventually_ge_atTop (25 : ℝ)] with r h1 h2 h3
  have hr0 : 0 < r := by linarith
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  refine ⟨h3, ?_, ?_⟩
  · rwa [le_div_iff₀ hs] at h1
  · have : P.f r / r * P.β < 1 := by rwa [lt_div_iff₀ hβ] at h2
    rw [mul_div_assoc, mul_comm]; linarith

lemma good_f (hP : P.Standing) (hg : Good P r) : (P.γ : ℝ) + 1 ≤ P.f r := by
  obtain ⟨h1, h2, -⟩ := hg
  have hγ1 : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have hs : 5 ≤ Real.sqrt r := by
    rw [show (5 : ℝ) = Real.sqrt 25 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h1
  nlinarith

/-- Uniform exponential domination of the normalized stationary law. -/
lemma G_dom (hP : P.Standing) (hg : Good P r) (q : ℤ → ℝ) (hq : IsArtStationary P r q) (u : ℝ) :
    q (Jr P r u) / q (kk P r) ≤ Real.exp (2 * (P.β * P.γ) - P.β * P.γ * |u| / 2) := by
  obtain ⟨h25, hfs, hf1⟩ := hg
  have hr0 : 0 < r := by linarith
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hβγ : 0 < P.β * P.γ := by
    have := hP.1; have : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
    positivity
  have hs1 : 1 ≤ Real.sqrt r := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hr1
  have hspos : 0 < Real.sqrt r := by linarith
  have hqk := qk_pos hP hr0 q hq
  obtain ⟨nb1, nb2⟩ := n_bounds P r u
  set n : ℤ := Jr P r u - kk P r with hn
  rcases le_or_gt 0 n with h0 | h0
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
    have hJ : Jr P r u = kk P r + N := by omega
    rw [hJ, prod_up hP hr0 q hq, mul_div_cancel_left₀ _ hqk.ne']
    refine le_trans (up_dom hP h25 (good_f hP ⟨h25, hfs, hf1⟩) N) (Real.exp_le_exp.mpr ?_)
    have hNr : (N : ℝ) = (n : ℝ) := by rw [hN]; rfl
    have hu : -1 < u := by
      have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h0
      have : -1 < u * Real.sqrt r := by linarith
      by_contra hc; push Not at hc; nlinarith
    have habs : |u| ≤ u + 2 := by
      rcases le_total 0 u with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    have : u / 2 - 1 / 2 ≤ (N : ℝ) / (2 * Real.sqrt r) := by
      rw [hNr, le_div_iff₀ (by positivity)]
      nlinarith
    have e : P.β * P.γ * (N : ℝ) / (2 * Real.sqrt r) = P.β * P.γ * ((N : ℝ) / (2 * Real.sqrt r)) := by ring
    rw [e]
    nlinarith
  · obtain ⟨M, hM⟩ : ∃ M : ℕ, -n = M := ⟨(-n).toNat, by omega⟩
    have hJ : Jr P r u = kk P r - M := by omega
    have hpd := prod_dn hP hr0 q hq M
    have hpp := prod_dn_pos hP hr0 M
    rw [← hJ] at hpd
    have : q (Jr P r u) / q (kk P r) = 1 / ∏ t ∈ Finset.range M, aa P r (kk P r - 1 - t) := by
      have hqJ : q (Jr P r u) ≠ 0 := by
        intro h; rw [h, zero_mul] at hpd; linarith
      rw [← hpd]; field_simp
    rw [this]
    refine le_trans (dn_dom hP hr1 hfs hf1 M) (Real.exp_le_exp.mpr ?_)
    have hMr : (M : ℝ) = -(n : ℝ) := by
      have : ((M : ℤ) : ℝ) = ((-n : ℤ) : ℝ) := by rw [hM]
      push_cast at this; linarith
    have hu : u < 0 := by
      have : (n : ℝ) ≤ -1 := by
        have : n ≤ -1 := by omega
        exact_mod_cast this
      by_contra hc; push Not at hc; nlinarith
    rw [abs_of_neg hu]
    have : -u / 2 - 1 / 2 ≤ (M : ℝ) / (2 * Real.sqrt r) := by
      rw [hMr, le_div_iff₀ (by positivity)]
      nlinarith
    have e : P.β * P.γ * (M : ℝ) / (2 * Real.sqrt r) = P.β * P.γ * ((M : ℝ) / (2 * Real.sqrt r)) := by ring
    rw [e]
    nlinarith

end GBSL5

-- ===== part L5d =====

open Filter Topology
open RandomLeadGBS.Diffusion

namespace GBSL5

/-- Asymptotics of `∑_{t<N} log(1 + ε ρ (t + d))` with `ρ = c/r` and `N/√r → w`. -/
lemma logsum_lim (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (N : ℝ → ℕ) (d : ℝ → ℝ)
    (w : ℝ) (hN : Tendsto (fun r => (N r : ℝ) / Real.sqrt r) atTop (𝓝 w))
    (hd : ∀ᶠ r in atTop, |d r| ≤ 3) :
    Tendsto (fun r => ∑ t ∈ Finset.range (N r), Real.log (1 + ε * (c / r) * ((t : ℝ) + d r)))
      atTop (𝓝 (ε * c * w ^ 2 / 2)) := by
  have hε1 : |ε| = 1 := by rcases hε with h | h <;> simp [h]
  set a : ℝ → ℝ := fun r => (N r : ℝ) / Real.sqrt r with ha
  have hinv : Tendsto (fun r : ℝ => 1 / Real.sqrt r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  -- main term
  set A : ℝ → ℝ := fun r => ε * (c / r) * (((N r : ℝ) * ((N r : ℝ) - 1) / 2) + d r * N r) with hA
  have hAe : ∀ᶠ r in atTop, A r = ε * c * (a r ^ 2 / 2 - a r * (1 / Real.sqrt r) / 2 +
      d r * (a r * (1 / Real.sqrt r))) := by
    filter_upwards [hpos] with r hr
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
    simp only [hA, ha]
    generalize Real.sqrt r = s at *
    subst hsq
    field_simp
  have hAlim : Tendsto A atTop (𝓝 (ε * c * w ^ 2 / 2)) := by
    have hd0 : Tendsto (fun r => d r * (a r * (1 / Real.sqrt r))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun r => a r * (1 / Real.sqrt r)) atTop (𝓝 0) := by
        simpa using hN.mul hinv
      refine squeeze_zero_norm' (a := fun r => 3 * ‖a r * (1 / Real.sqrt r)‖) ?_ ?_
      · filter_upwards [hd] with r hr
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)
      · simpa using (h1.norm.const_mul 3)
    have h2 : Tendsto (fun r => ε * c * (a r ^ 2 / 2 - a r * (1 / Real.sqrt r) / 2 +
        d r * (a r * (1 / Real.sqrt r)))) atTop (𝓝 (ε * c * (w ^ 2 / 2 - w * 0 / 2 + 0))) :=
      ((((hN.pow 2).div_const 2).sub ((hN.mul hinv).div_const 2)).add hd0).const_mul _
    simp only [mul_zero, zero_div, sub_zero, add_zero] at h2
    rw [show ε * c * w ^ 2 / 2 = ε * c * (w ^ 2 / 2) by ring]
    exact h2.congr' (hAe.mono fun r h => h.symm)
  -- error term
  set B : ℝ → ℝ := fun r => 2 * (N r : ℝ) * ((c / r) * ((N r : ℝ) + 3)) ^ 2 with hB
  have hBlim : Tendsto B atTop (𝓝 0) := by
    have hBe : ∀ᶠ r in atTop, B r = 2 * c ^ 2 * (a r * (a r + 3 * (1 / Real.sqrt r)) ^ 2) *
        (1 / Real.sqrt r) := by
      filter_upwards [hpos] with r hr
      have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
      simp only [hB, ha]
      generalize Real.sqrt r = s at *
      subst hsq
      field_simp
    have := (((hN.mul ((hN.add (hinv.const_mul 3)).pow 2)).const_mul (2 * c ^ 2)).mul hinv)
    simp only [mul_zero] at this
    exact this.congr' (hBe.mono fun r h => h.symm)
  -- smallness of the increments
  have hsmall : Tendsto (fun r => (c / r) * ((N r : ℝ) + 3)) atTop (𝓝 0) := by
    have he : ∀ᶠ r in atTop, (c / r) * ((N r : ℝ) + 3) =
        c * (a r * (1 / Real.sqrt r) + 3 * (1 / Real.sqrt r) ^ 2) := by
      filter_upwards [hpos] with r hr
      have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
      simp only [ha]
      generalize Real.sqrt r = s at *
      subst hsq
      field_simp
    have := ((hN.mul hinv).add ((hinv.pow 2).const_mul 3)).const_mul c
    simp only [mul_zero, add_zero, zero_pow two_ne_zero] at this
    exact this.congr' (he.mono fun r h => h.symm)
  have hsm : ∀ᶠ r in atTop, (c / r) * ((N r : ℝ) + 3) ≤ 1 / 2 :=
    hsmall.eventually (ge_mem_nhds (by norm_num))
  -- combine
  have hEb : ∀ᶠ r in atTop, |∑ t ∈ Finset.range (N r), Real.log (1 + ε * (c / r) * ((t : ℝ) + d r)) -
      A r| ≤ B r := by
    filter_upwards [hsm, hd, hpos] with r hsm hd hr
    have hcr : 0 < c / r := by positivity
    have hAs : A r = ∑ t ∈ Finset.range (N r), ε * (c / r) * ((t : ℝ) + d r) := by
      simp only [hA]
      rw [show (fun t : ℕ => ε * (c / r) * ((t : ℝ) + d r)) =
        fun t : ℕ => (ε * (c / r)) * (t : ℝ) + ε * (c / r) * d r from funext fun t => by ring]
      rw [sum_lin]; ring
    rw [hAs, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ t ∈ Finset.range (N r), |Real.log (1 + ε * (c / r) * ((t : ℝ) + d r)) -
        ε * (c / r) * ((t : ℝ) + d r)| ≤ 2 * ((c / r) * ((N r : ℝ) + 3)) ^ 2 := by
      intro t ht
      have htN : (t : ℝ) + 1 ≤ N r := by
        have := Finset.mem_range.mp ht; exact_mod_cast this
      set x := -(ε * (c / r) * ((t : ℝ) + d r))
      have hx : |x| ≤ (c / r) * ((N r : ℝ) + 3) := by
        simp only [x, abs_neg, abs_mul, hε1, one_mul, abs_of_pos hcr]
        apply mul_le_mul_of_nonneg_left _ hcr.le
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ t)]; linarith
      have hlb := log_bound x (le_trans hx hsm)
      have e : 1 + ε * (c / r) * ((t : ℝ) + d r) = 1 - x := by simp only [x]; ring
      rw [e, show Real.log (1 - x) - ε * (c / r) * ((t : ℝ) + d r) = Real.log (1 - x) + x by
        simp only [x]; ring]
      refine le_trans hlb ?_
      have : x ^ 2 ≤ ((c / r) * ((N r : ℝ) + 3)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [hB]; ring_nf; exact le_refl _
  have hdiff : Tendsto (fun r => ∑ t ∈ Finset.range (N r), Real.log (1 + ε * (c / r) * ((t : ℝ) + d r)) -
      A r) atTop (𝓝 0) := squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hEb) hBlim
  have := hdiff.add hAlim
  simpa using this

end GBSL5

-- ===== part L5e =====

open Filter Topology
open RandomLeadGBS.Diffusion

namespace GBSL5

variable {P : Params}

lemma small_lim (c : ℝ) (N : ℝ → ℕ) (w : ℝ)
    (hN : Tendsto (fun r => (N r : ℝ) / Real.sqrt r) atTop (𝓝 w)) :
    Tendsto (fun r => (c / r) * ((N r : ℝ) + 3)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun r : ℝ => 1 / Real.sqrt r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have he : ∀ᶠ r in atTop, (c / r) * ((N r : ℝ) + 3) =
      c * ((N r : ℝ) / Real.sqrt r * (1 / Real.sqrt r) + 3 * (1 / Real.sqrt r) ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
    generalize Real.sqrt r = s at *
    subst hsq
    field_simp
  have := ((hN.mul hinv).add ((hinv.pow 2).const_mul 3)).const_mul c
  simp only [mul_zero, add_zero, zero_pow two_ne_zero] at this
  exact this.congr' (he.mono fun r h => h.symm)

lemma N_lim (P : Params) (u : ℝ) (N : ℝ → ℕ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hN : ∀ᶠ r in atTop, (N r : ℝ) = σ * (((Jr P r u - kk P r : ℤ)) : ℝ)) :
    Tendsto (fun r => (N r : ℝ) / Real.sqrt r) atTop (𝓝 (σ * u)) := by
  have hinv : Tendsto (fun r : ℝ => 1 / Real.sqrt r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hs1 : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hinv
  filter_upwards [hN, eventually_gt_atTop (0 : ℝ)] with r hNr hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  obtain ⟨b1, b2⟩ := n_bounds P r u
  rw [norm_norm, Real.norm_eq_abs, hNr]
  rw [show σ * (((Jr P r u - kk P r : ℤ)) : ℝ) / Real.sqrt r - σ * u =
    σ * ((((Jr P r u - kk P r : ℤ)) : ℝ) - u * Real.sqrt r) / Real.sqrt r by field_simp]
  rw [abs_div, abs_mul, hs1, one_mul, abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  rw [abs_le]; constructor <;> linarith

/-- Pointwise local limit: `q_r(⌊x∗ + u√r⌋)/q_r(k) → exp(−βγ u²/2)`. -/
theorem G_lim (hP : P.Standing) (q : ℝ → ℤ → ℝ) (hq : ∀ᶠ r in atTop, IsArtStationary P r (q r))
    (u : ℝ) :
    Tendsto (fun r => q r (Jr P r u) / q r (kk P r)) atTop
      (𝓝 (Real.exp (-(P.β * P.γ) * u ^ 2 / 2))) := by
  have hβγ : 0 < P.β * P.γ := by
    have := hP.1; have : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
    positivity
  have hgood := good_ev hP
  rcases lt_trichotomy u 0 with hu | hu | hu
  · -- negative side
    set N : ℝ → ℕ := fun r => (kk P r - Jr P r u).toNat with hNd
    have hn : ∀ r, Jr P r u - kk P r ≤ 0 := by
      intro r
      obtain ⟨-, b2⟩ := n_bounds P r u
      have : u * Real.sqrt r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu.le (Real.sqrt_nonneg r)
      have : (((Jr P r u - kk P r : ℤ)) : ℝ) < 1 := by linarith
      have : Jr P r u - kk P r < 1 := by exact_mod_cast this
      omega
    have hNe : ∀ r, (N r : ℝ) = (-1) * (((Jr P r u - kk P r : ℤ)) : ℝ) := by
      intro r
      have := hn r
      simp only [hNd]
      have : ((kk P r - Jr P r u).toNat : ℤ) = kk P r - Jr P r u := Int.toNat_of_nonneg (by omega)
      have : (((kk P r - Jr P r u).toNat : ℕ) : ℝ) = (((kk P r - Jr P r u : ℤ)) : ℝ) := by
        exact_mod_cast this
      rw [this]; push_cast; ring
    have hNl := N_lim P u N (-1) (Or.inr rfl) (Eventually.of_forall hNe)
    have hlog := logsum_lim (P.β * P.γ) hβγ 1 (Or.inl rfl) N
      (fun r => ist P r - kk P r + 1) (-1 * u) hNl
      (Eventually.of_forall fun r => by
        have := kk_bounds (r := r) hP
        rw [abs_le]; constructor <;> linarith)
    have hsm := small_lim (P.β * P.γ) N (-1 * u) hNl
    -- the cap is not reached
    have hcap : ∀ᶠ r in atTop, (P.β * P.γ / r) * ((N r : ℝ) + 3) ≤ P.β * P.f r / r := by
      have hfs := hP.2.2.2.2
      have h1 : ∀ᶠ r in atTop, (P.γ : ℝ) * (-u + 4) ≤ P.f r / Real.sqrt r :=
        hfs.eventually (eventually_ge_atTop _)
      filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with r h1 hr1
      have hr : 0 < r := by linarith
      have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      have hs1 : 1 ≤ Real.sqrt r := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hr1
      obtain ⟨b1, -⟩ := n_bounds P r u
      have hNb : (N r : ℝ) + 3 ≤ (-u + 4) * Real.sqrt r := by
        rw [hNe r]
        have : (-1) * (((Jr P r u - kk P r : ℤ)) : ℝ) + 3 ≤ -u * Real.sqrt r + 4 := by linarith
        have : -u * Real.sqrt r + 4 ≤ (-u + 4) * Real.sqrt r := by nlinarith
        linarith
      rw [le_div_iff₀ hs] at h1
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr]
      have := hP.1
      have hγ0 : (0 : ℝ) ≤ P.γ := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hNb hγ0]
    have hsmall : ∀ᶠ r in atTop, (P.β * P.γ / r) * ((N r : ℝ) + 3) ≤ 1 / 2 :=
      hsm.eventually (ge_mem_nhds (by norm_num))
    have heq : ∀ᶠ r in atTop, q r (Jr P r u) / q r (kk P r) =
        Real.exp (-(∑ t ∈ Finset.range (N r),
          Real.log (1 + 1 * (P.β * P.γ / r) * ((t : ℝ) + (ist P r - kk P r + 1))))) := by
      filter_upwards [hq, hgood, hcap, hsmall] with r hqr hg hcap hsmall
      have hr0 : 0 < r := by linarith [hg.1]
      have hk := kk_bounds (r := r) hP
      have hJ : Jr P r u = kk P r - N r := by
        have := hn r; simp only [hNd]; omega
      have hpd := prod_dn hP hr0 (q r) hqr (N r)
      rw [← hJ] at hpd
      have hterm : ∀ t ∈ Finset.range (N r), aa P r (kk P r - 1 - t) =
          1 + 1 * (P.β * P.γ / r) * ((t : ℝ) + (ist P r - kk P r + 1)) := by
        intro t ht
        have htN : (t : ℝ) + 1 ≤ N r := by have := Finset.mem_range.mp ht; exact_mod_cast this
        rw [aa_dn hP hr0 _ (aI_low_nonneg hP hr0 _ (by omega))]
        have e : 1 - rho P r * ((((kk P r - 1 - t : ℤ)) : ℝ) - ist P r) =
            1 + 1 * (P.β * P.γ / r) * ((t : ℝ) + (ist P r - kk P r + 1)) := by
          unfold rho; push_cast; ring
        rw [e]
        apply min_eq_left
        have hb := bm_ge hP hr0
        have : (P.β * P.γ / r) * ((t : ℝ) + (ist P r - kk P r + 1)) ≤
            (P.β * P.γ / r) * ((N r : ℝ) + 3) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        linarith
      have hpos : ∀ t ∈ Finset.range (N r), 0 < 1 + 1 * (P.β * P.γ / r) * ((t : ℝ) + (ist P r - kk P r + 1)) := by
        intro t _; have : 0 ≤ (P.β * P.γ / r) * ((t : ℝ) + (ist P r - kk P r + 1)) := by
          apply mul_nonneg (by positivity); linarith [kk_bounds (r := r) hP]
        linarith
      rw [Real.exp_neg, Real.exp_sum, Finset.prod_congr rfl (fun t ht => Real.exp_log (hpos t ht)),
        ← Finset.prod_congr rfl hterm]
      have hP0 : 0 < ∏ t ∈ Finset.range (N r), aa P r (kk P r - 1 - t) :=
        lt_of_lt_of_le one_pos (prod_dn_pos hP hr0 _)
      have hqk := qk_pos hP hr0 (q r) hqr
      have hqJ : q r (Jr P r u) ≠ 0 := by
        intro h; rw [h, zero_mul] at hpd; linarith
      rw [← hpd]; field_simp
    have : Tendsto (fun r => Real.exp (-(∑ t ∈ Finset.range (N r),
        Real.log (1 + 1 * (P.β * P.γ / r) * ((t : ℝ) + (ist P r - kk P r + 1)))))) atTop
        (𝓝 (Real.exp (-(1 * (P.β * P.γ) * (-1 * u) ^ 2 / 2)))) :=
      (Real.continuous_exp.tendsto _).comp hlog.neg
    rw [show -(P.β * P.γ) * u ^ 2 / 2 = -(1 * (P.β * P.γ) * (-1 * u) ^ 2 / 2) by ring]
    exact this.congr' (heq.mono fun r h => h.symm)
  · -- u = 0
    subst hu
    have heq : ∀ᶠ r in atTop, q r (Jr P r 0) / q r (kk P r) = 1 := by
      filter_upwards [hq, hgood] with r hqr hg
      have hr0 : 0 < r := by linarith [hg.1]
      have : Jr P r 0 = kk P r := by unfold Jr kk; simp
      rw [this, div_self (qk_pos hP hr0 (q r) hqr).ne']
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      Real.exp_zero]
    exact tendsto_const_nhds.congr' (heq.mono fun r h => h.symm)
  · -- positive side
    set N : ℝ → ℕ := fun r => (Jr P r u - kk P r).toNat with hNd
    have hn : ∀ r, 0 ≤ Jr P r u - kk P r := by
      intro r
      obtain ⟨b1, -⟩ := n_bounds P r u
      have : 0 ≤ u * Real.sqrt r := mul_nonneg hu.le (Real.sqrt_nonneg r)
      have : (-1 : ℝ) < (((Jr P r u - kk P r : ℤ)) : ℝ) := by linarith
      have : -1 < Jr P r u - kk P r := by exact_mod_cast this
      omega
    have hNe : ∀ r, (N r : ℝ) = 1 * (((Jr P r u - kk P r : ℤ)) : ℝ) := by
      intro r
      have : ((Jr P r u - kk P r).toNat : ℤ) = Jr P r u - kk P r := Int.toNat_of_nonneg (hn r)
      have : (((Jr P r u - kk P r).toNat : ℕ) : ℝ) = (((Jr P r u - kk P r : ℤ)) : ℝ) := by
        exact_mod_cast this
      simp only [hNd]; rw [this]; ring
    have hNl := N_lim P u N 1 (Or.inl rfl) (Eventually.of_forall hNe)
    have hlog := logsum_lim (P.β * P.γ) hβγ (-1) (Or.inr rfl) N
      (fun r => (kk P r : ℝ) - ist P r) (1 * u) hNl
      (Eventually.of_forall fun r => by
        have := kk_bounds (r := r) hP
        rw [abs_le]; constructor <;> linarith)
    have hsm := small_lim (P.β * P.γ) N (1 * u) hNl
    have hsmall : ∀ᶠ r in atTop, (P.β * P.γ / r) * ((N r : ℝ) + 3) ≤ 1 / 2 :=
      hsm.eventually (ge_mem_nhds (by norm_num))
    have heq : ∀ᶠ r in atTop, q r (Jr P r u) / q r (kk P r) =
        Real.exp (∑ t ∈ Finset.range (N r),
          Real.log (1 + -1 * (P.β * P.γ / r) * ((t : ℝ) + ((kk P r : ℝ) - ist P r)))) := by
      filter_upwards [hq, hgood, hsmall] with r hqr hg hsmall
      have hr0 : 0 < r := by linarith [hg.1]
      have hk := kk_bounds (r := r) hP
      have hJ : Jr P r u = kk P r + N r := by
        have := hn r; simp only [hNd]; omega
      have hterm : ∀ t ∈ Finset.range (N r), aa P r (kk P r + t) =
          1 + -1 * (P.β * P.γ / r) * ((t : ℝ) + ((kk P r : ℝ) - ist P r)) := by
        intro t ht
        have htN : (t : ℝ) + 1 ≤ N r := by have := Finset.mem_range.mp ht; exact_mod_cast this
        rw [aa_up hP hr0 _ (aI_le_m hP hr0 (good_f hP hg) _ (by omega))]
        have e : 1 - rho P r * ((((kk P r + t : ℤ)) : ℝ) - ist P r) =
            1 + -1 * (P.β * P.γ / r) * ((t : ℝ) + ((kk P r : ℝ) - ist P r)) := by
          unfold rho; push_cast; ring
        rw [e]
        apply max_eq_left
        have : (P.β * P.γ / r) * ((t : ℝ) + ((kk P r : ℝ) - ist P r)) ≤
            (P.β * P.γ / r) * ((N r : ℝ) + 3) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        linarith
      have hpos : ∀ t ∈ Finset.range (N r),
          0 < 1 + -1 * (P.β * P.γ / r) * ((t : ℝ) + ((kk P r : ℝ) - ist P r)) := by
        intro t ht
        have htN : (t : ℝ) + 1 ≤ N r := by have := Finset.mem_range.mp ht; exact_mod_cast this
        have : (P.β * P.γ / r) * ((t : ℝ) + ((kk P r : ℝ) - ist P r)) ≤
            (P.β * P.γ / r) * ((N r : ℝ) + 3) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        linarith
      rw [Real.exp_sum, Finset.prod_congr rfl (fun t ht => Real.exp_log (hpos t ht)),
        ← Finset.prod_congr rfl hterm, hJ, prod_up hP hr0 (q r) hqr,
        mul_div_cancel_left₀ _ (qk_pos hP hr0 (q r) hqr).ne']
    have : Tendsto (fun r => Real.exp (∑ t ∈ Finset.range (N r),
        Real.log (1 + -1 * (P.β * P.γ / r) * ((t : ℝ) + ((kk P r : ℝ) - ist P r))))) atTop
        (𝓝 (Real.exp (-1 * (P.β * P.γ) * (1 * u) ^ 2 / 2))) :=
      (Real.continuous_exp.tendsto _).comp hlog
    rw [show -(P.β * P.γ) * u ^ 2 / 2 = -1 * (P.β * P.γ) * (1 * u) ^ 2 / 2 by ring]
    exact this.congr' (heq.mono fun r h => h.symm)

end GBSL5

-- ===== part L5f =====

open Filter Topology MeasureTheory
open RandomLeadGBS.Diffusion

namespace GBSL5

variable {P : Params} {r : ℝ}

noncomputable def ut (P : Params) (r u : ℝ) : ℝ := (((Jr P r u : ℤ) : ℝ) - P.xs r) / Real.sqrt r

lemma ut_close (hr : 0 < r) (u : ℝ) : |ut P r u - u| ≤ 1 / Real.sqrt r := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have h1 := Int.floor_le (P.xs r + u * Real.sqrt r)
  have h2 := Int.lt_floor_add_one (P.xs r + u * Real.sqrt r)
  unfold ut Jr
  rw [show (((⌊P.xs r + u * Real.sqrt r⌋ : ℤ) : ℝ) - P.xs r) / Real.sqrt r - u =
    ((((⌊P.xs r + u * Real.sqrt r⌋ : ℤ) : ℝ) - P.xs r) - u * Real.sqrt r) / Real.sqrt r by
    field_simp]
  rw [abs_div, abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  rw [abs_le]; constructor <;> linarith

/-- The step function `u ↦ (q(⌊x∗+u√r⌋)/q(k)) h(ũ)`. -/
noncomputable def Phi (P : Params) (q : ℤ → ℝ) (h : ℝ → ℝ) (r u : ℝ) : ℝ :=
  q (Jr P r u) / q (kk P r) * h (ut P r u)

lemma Jr_measurable (P : Params) (r : ℝ) : Measurable (fun u => Jr P r u) := by
  unfold Jr
  exact Int.measurable_floor.comp (measurable_const.add (measurable_id.mul measurable_const))

lemma Phi_measurable (P : Params) (q : ℤ → ℝ) (h : ℝ → ℝ) (hh : Continuous h) (r : ℝ) :
    Measurable (Phi P q h r) := by
  unfold Phi ut
  have hJ := Jr_measurable P r
  have h1 : Measurable (fun u => q (Jr P r u) / q (kk P r)) :=
    (measurable_of_countable (fun j : ℤ => q j / q (kk P r))).comp hJ
  have h2 : Measurable (fun u => (((Jr P r u : ℤ) : ℝ) - P.xs r) / Real.sqrt r) :=
    ((measurable_of_countable (fun j : ℤ => ((j : ℝ) - P.xs r) / Real.sqrt r)).comp hJ)
  exact h1.mul (hh.measurable.comp h2)

lemma poly_exp (b : ℝ) (hb : 0 < b) (x : ℝ) (hx : 0 ≤ x) :
    (2 + x) * (1 + x ^ 2) ≤ (2 + 1 / b + 4 / b ^ 2 + 6 / b ^ 3) * Real.exp (b * x) := by
  have e1 := Real.pow_div_factorial_le_exp (b * x) (by positivity) 1
  have e2 := Real.pow_div_factorial_le_exp (b * x) (by positivity) 2
  have e3 := Real.pow_div_factorial_le_exp (b * x) (by positivity) 3
  have e0 := Real.one_le_exp (by positivity : (0 : ℝ) ≤ b * x)
  simp only [Nat.factorial, Nat.cast_one, Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_ofNat] at e1 e2 e3
  norm_num at e1 e2 e3
  set E := Real.exp (b * x)
  have k1 : x ≤ E / b := by rw [le_div_iff₀ hb]; linarith
  have k2 : x ^ 2 ≤ 2 * E / b ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have k3 : x ^ 3 ≤ 6 * E / b ^ 3 := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have : (2 + x) * (1 + x ^ 2) = 2 + x + 2 * x ^ 2 + x ^ 3 := by ring
  rw [this]
  have : (2 + 1 / b + 4 / b ^ 2 + 6 / b ^ 3) * E = 2 * E + E / b + 2 * (2 * E / b ^ 2) + 6 * E / b ^ 3 := by
    field_simp; ring
  rw [this]
  linarith

lemma bound_integrable (b A C : ℝ) (hb : 0 < b) :
    Integrable (fun u : ℝ => Real.exp (A - b * |u|) * (C * (2 + |u|))) := by
  have hK := integrable_inv_one_add_sq.const_mul (|Real.exp A * C| * (2 + 1 / b + 4 / b ^ 2 + 6 / b ^ 3))
  refine Integrable.mono' hK ?_ (Eventually.of_forall fun u => ?_)
  · exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (A - b * |u|) * (C * (2 + |u|)))).aestronglyMeasurable
  · have hp := poly_exp b hb |u| (abs_nonneg u)
    rw [sq_abs] at hp
    have hpos : 0 < 1 + u ^ 2 := by positivity
    have he : Real.exp (A - b * |u|) = Real.exp A / Real.exp (b * |u|) := by
      rw [Real.exp_sub]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, he, abs_div, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity : (0 : ℝ) < 2 + |u|)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos _)]
    have hk0 : 0 ≤ 2 + 1 / b + 4 / b ^ 2 + 6 / b ^ 3 := by positivity
    have : |C| * (2 + |u|) ≤ |C| * ((2 + 1 / b + 4 / b ^ 2 + 6 / b ^ 3) * Real.exp (b * |u|)) / (1 + u ^ 2) := by
      rw [le_div_iff₀ hpos]
      have := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
      nlinarith
    calc Real.exp A * (|C| * (2 + |u|)) ≤ Real.exp A * (|C| * ((2 + 1 / b + 4 / b ^ 2 + 6 / b ^ 3) *
          Real.exp (b * |u|)) / (1 + u ^ 2)) := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = |Real.exp A * C| * (2 + 1 / b + 4 / b ^ 2 + 6 / b ^ 3) * (1 + u ^ 2)⁻¹ * Real.exp (b * |u|) := by
          rw [abs_mul, abs_of_pos (Real.exp_pos A)]; field_simp
      _ = _ := rfl

end GBSL5

-- ===== part L5g =====

open Filter Topology MeasureTheory
open RandomLeadGBS.Diffusion

namespace GBSL5

variable {P : Params} {r : ℝ}

lemma Phi_bound (hP : P.Standing) (hg : Good P r) (q : ℤ → ℝ) (hq : IsArtStationary P r q)
    (h : ℝ → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |h x| ≤ C * (1 + |x|)) (u : ℝ) :
    ‖Phi P q h r u‖ ≤ Real.exp (2 * (P.β * P.γ) - (P.β * P.γ / 2) * |u|) * (C * (2 + |u|)) := by
  have hr0 : 0 < r := by linarith [hg.1]
  have hr1 : (1 : ℝ) ≤ r := by linarith [hg.1]
  have hs1 : 1 ≤ Real.sqrt r := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hr1
  have hqk := qk_pos hP hr0 q hq
  have hratio0 : 0 ≤ q (Jr P r u) / q (kk P r) := div_nonneg (hq.1 _) hqk.le
  have hG := G_dom hP hg q hq u
  have hcl := ut_close (P := P) hr0 u
  have h1 : 1 / Real.sqrt r ≤ 1 := by rw [div_le_one (by linarith)]; exact hs1
  have hut : |ut P r u| ≤ |u| + 1 := by
    have := abs_sub_abs_le_abs_sub (ut P r u) u
    linarith
  unfold Phi
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hratio0]
  have e : 2 * (P.β * P.γ) - (P.β * P.γ / 2) * |u| = 2 * (P.β * P.γ) - P.β * P.γ * |u| / 2 := by ring
  rw [e]
  apply mul_le_mul hG _ (abs_nonneg _) (Real.exp_pos _).le
  refine le_trans (hC _) ?_
  apply mul_le_mul_of_nonneg_left _ hC0
  linarith

lemma sum_identity (hP : P.Standing) (hg : Good P r) (q : ℤ → ℝ) (hq : IsArtStationary P r q)
    (h : ℝ → ℝ) (hh : Continuous h) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |h x| ≤ C * (1 + |x|)) :
    Integrable (Phi P q h r) ∧
    HasSum (fun j : ℤ => q j * h (((j : ℝ) - P.xs r) / Real.sqrt r))
      (q (kk P r) * Real.sqrt r * ∫ u, Phi P q h r u) := by
  have hr0 : 0 < r := by linarith [hg.1]
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hβγ : 0 < P.β * P.γ := by
    have := hP.1; have : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
    positivity
  have hqk := qk_pos hP hr0 q hq
  have hint : Integrable (Phi P q h r) := by
    refine Integrable.mono' (bound_integrable (P.β * P.γ / 2) (2 * (P.β * P.γ)) C (by positivity))
      (Phi_measurable P q h hh r).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    exact Phi_bound hP hg q hq h C hC0 hC u
  refine ⟨hint, ?_⟩
  set s : ℤ → Set ℝ := fun j => Set.Ico (((j : ℝ) - P.xs r) / Real.sqrt r) (((j : ℝ) + 1 - P.xs r) / Real.sqrt r)
    with hsdef
  have hmem : ∀ j u, u ∈ s j ↔ Jr P r u = j := by
    intro j u
    simp only [hsdef, Set.mem_Ico, Jr]
    rw [Int.floor_eq_iff, div_le_iff₀ hs, lt_div_iff₀ hs]
    constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  have hmeas : ∀ j, MeasurableSet (s j) := fun j => measurableSet_Ico
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro u hu hu'
    exact hij (((hmem i u).mp hu).symm.trans ((hmem j u).mp hu'))
  have hunion : (⋃ j, s j) = Set.univ := by
    ext u; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨Jr P r u, (hmem _ u).mpr rfl⟩
  have hsum := hasSum_integral_iUnion hmeas hdisj (by rw [hunion]; exact hint.integrableOn)
  rw [hunion, Measure.restrict_univ] at hsum
  have hpiece : ∀ j : ℤ, ∫ u in s j, Phi P q h r u =
      q j / q (kk P r) * h (((j : ℝ) - P.xs r) / Real.sqrt r) * (1 / Real.sqrt r) := by
    intro j
    rw [setIntegral_congr_fun (hmeas j) (g := fun _ => q j / q (kk P r) * h (((j : ℝ) - P.xs r) / Real.sqrt r))
      (fun u hu => by
        have := (hmem j u).mp hu
        simp only [Phi, ut, this])]
    rw [setIntegral_const, smul_eq_mul, Measure.real, hsdef, Real.volume_Ico,
      ENNReal.toReal_ofReal (by
        rw [← sub_div]; apply div_nonneg _ hs.le; linarith)]
    rw [← sub_div]
    field_simp
    ring
  simp only [hpiece] at hsum
  have := hsum.mul_left (q (kk P r) * Real.sqrt r)
  have e : (fun j : ℤ => q (kk P r) * Real.sqrt r *
      (q j / q (kk P r) * h (((j : ℝ) - P.xs r) / Real.sqrt r) * (1 / Real.sqrt r))) =
      fun j : ℤ => q j * h (((j : ℝ) - P.xs r) / Real.sqrt r) := by
    funext j; field_simp
  rw [e] at this
  exact this

end GBSL5

-- ===== part L5h =====

open Filter Topology MeasureTheory ProbabilityTheory
open RandomLeadGBS.Diffusion

namespace GBSL5

variable {P : Params}

lemma Phi_lim (hP : P.Standing) (q : ℝ → ℤ → ℝ) (hq : ∀ᶠ r in atTop, IsArtStationary P r (q r))
    (h : ℝ → ℝ) (hh : Continuous h) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |h x| ≤ C * (1 + |x|)) :
    Tendsto (fun r => ∫ u, Phi P (q r) h r u) atTop
      (𝓝 (∫ u, Real.exp (-(P.β * P.γ) * u ^ 2 / 2) * h u)) := by
  have hβγ : 0 < P.β * P.γ := by
    have := hP.1; have : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
    positivity
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u => Real.exp (2 * (P.β * P.γ) - (P.β * P.γ / 2) * |u|) * (C * (2 + |u|)))
  · exact Eventually.of_forall fun r => (Phi_measurable P (q r) h hh r).aestronglyMeasurable
  · filter_upwards [hq, good_ev hP] with r hqr hg
    exact Eventually.of_forall fun u => Phi_bound hP hg (q r) hqr h C hC0 hC u
  · exact bound_integrable _ _ _ (by positivity)
  · refine Eventually.of_forall fun u => ?_
    have hG := G_lim hP q hq u
    have hut : Tendsto (fun r => ut P r u) atTop (𝓝 u) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero_norm' ?_ ((tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop :
        Tendsto (fun r : ℝ => (1 : ℝ) / Real.sqrt r) atTop (𝓝 0)))
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      rw [norm_norm, Real.norm_eq_abs]
      exact ut_close hr u
    exact hG.mul ((hh.tendsto u).comp hut)

lemma gauss_int (hP : P.Standing) (h : ℝ → ℝ) (hint : Integrable h (gaussianReal 0 (1 / (P.β * P.γ)).toNNReal)) :
    ∫ x, h x ∂(gaussianReal 0 (1 / (P.β * P.γ)).toNNReal) =
      (∫ u, Real.exp (-(P.β * P.γ) * u ^ 2 / 2) * h u) / ∫ u, Real.exp (-(P.β * P.γ) * u ^ 2 / 2) := by
  have hβγ : 0 < P.β * P.γ := by
    have := hP.1; have : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
    positivity
  have hvval : (((1 / (P.β * P.γ)).toNNReal : NNReal) : ℝ) = 1 / (P.β * P.γ) :=
    Real.coe_toNNReal _ (by positivity)
  have hv : (1 / (P.β * P.γ)).toNNReal ≠ 0 := by
    intro h0
    have : (((1 / (P.β * P.γ)).toNNReal : NNReal) : ℝ) = 0 := by rw [h0]; rfl
    rw [hvval] at this
    have : 0 < 1 / (P.β * P.γ) := by positivity
    linarith
  rw [integral_gaussianReal_eq_integral_smul hv]
  have hE : ∫ u, Real.exp (-(P.β * P.γ) * u ^ 2 / 2) = Real.sqrt (2 * Real.pi / (P.β * P.γ)) := by
    have := integral_gaussian (P.β * P.γ / 2)
    rw [show (fun u : ℝ => Real.exp (-(P.β * P.γ) * u ^ 2 / 2)) =
      fun u => Real.exp (-(P.β * P.γ / 2) * u ^ 2) from funext fun u => by ring_nf]
    rw [this]; congr 1; field_simp
  rw [hE]
  have hpdf : ∀ x, gaussianPDFReal 0 (1 / (P.β * P.γ)).toNNReal x =
      (Real.sqrt (2 * Real.pi / (P.β * P.γ)))⁻¹ * Real.exp (-(P.β * P.γ) * x ^ 2 / 2) := by
    intro x
    simp only [gaussianPDFReal, hvval, sub_zero]
    congr 2
    · congr 1; field_simp
    · field_simp
  simp only [hpdf, smul_eq_mul]
  rw [show (fun x => (Real.sqrt (2 * Real.pi / (P.β * P.γ)))⁻¹ * Real.exp (-(P.β * P.γ) * x ^ 2 / 2) * h x) =
    fun x => (Real.sqrt (2 * Real.pi / (P.β * P.γ)))⁻¹ * (Real.exp (-(P.β * P.γ) * x ^ 2 / 2) * h x) from
    funext fun x => by ring, integral_const_mul]
  ring

/-- The diffusion limit for continuous test functions of linear growth. -/
theorem main_lim (hP : P.Standing) (q : ℝ → ℤ → ℝ) (hq : ∀ᶠ r in atTop, IsArtStationary P r (q r))
    (h : ℝ → ℝ) (hh : Continuous h) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |h x| ≤ C * (1 + |x|))
    (hint : Integrable h (gaussianReal 0 (1 / (P.β * P.γ)).toNNReal)) :
    Tendsto (fun r => ∑' j : ℤ, q r j * h (((j : ℝ) - P.xs r) / Real.sqrt r)) atTop
      (𝓝 (∫ x, h x ∂(gaussianReal 0 (1 / (P.β * P.γ)).toNNReal))) := by
  have hβγ : 0 < P.β * P.γ := by
    have := hP.1; have : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
    positivity
  have h1c : ∀ x : ℝ, |(fun _ : ℝ => (1 : ℝ)) x| ≤ 1 * (1 + |x|) := fun x => by
    simp
  have Ih := Phi_lim hP q hq h hh C hC0 hC
  have I1 := Phi_lim hP q hq (fun _ => 1) continuous_const 1 zero_le_one h1c
  simp only [mul_one] at I1
  have hEpos : 0 < ∫ u, Real.exp (-(P.β * P.γ) * u ^ 2 / 2) := by
    have := integral_gaussian (P.β * P.γ / 2)
    rw [show (fun u : ℝ => Real.exp (-(P.β * P.γ) * u ^ 2 / 2)) =
      fun u => Real.exp (-(P.β * P.γ / 2) * u ^ 2) from funext fun u => by ring_nf, this]
    apply Real.sqrt_pos.mpr; positivity
  rw [gauss_int hP h hint]
  have hlim := Ih.div I1 hEpos.ne'
  refine hlim.congr' ?_
  filter_upwards [hq, good_ev hP] with r hqr hg
  have hr0 : 0 < r := by linarith [hg.1]
  obtain ⟨-, hs⟩ := sum_identity hP hg (q r) hqr h hh C hC0 hC
  obtain ⟨-, hs1⟩ := sum_identity hP hg (q r) hqr (fun _ => 1) continuous_const 1 zero_le_one h1c
  simp only [mul_one] at hs1
  have h1 : q r (kk P r) * Real.sqrt r * ∫ u, Phi P (q r) (fun _ => 1) r u = 1 := by
    rw [← hs1.tsum_eq]; exact hqr.2.2.1
  rw [hs.tsum_eq]
  have hne : ∫ u, Phi P (q r) (fun _ => 1) r u ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
  have hk : q r (kk P r) * Real.sqrt r = 1 / ∫ u, Phi P (q r) (fun _ => 1) r u := by
    rw [eq_div_iff hne]; exact h1
  rw [hk]; simp only [Pi.div_apply]; ring

end GBSL5

-- ===== part L5i =====

open Filter Topology
open RandomLeadGBS.Diffusion

namespace GBSL5

variable {P : Params} {r : ℝ}

/-- Unnormalized product-form weights. -/
noncomputable def wf (P : Params) (r : ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j - kk P r then ∏ t ∈ Finset.range (j - kk P r).toNat, aa P r (kk P r + t)
  else 1 / ∏ t ∈ Finset.range (kk P r - j).toNat, aa P r (kk P r - 1 - t)

lemma wf_rec (hP : P.Standing) (hr : 0 < r) (j : ℤ) : wf P r (j + 1) = aa P r j * wf P r j := by
  unfold wf
  by_cases h : 0 ≤ j - kk P r
  · rw [if_pos (by omega), if_pos h]
    have e : (j + 1 - kk P r).toNat = (j - kk P r).toNat + 1 := by omega
    rw [e, Finset.prod_range_succ]
    have e2 : kk P r + ((j - kk P r).toNat : ℤ) = j := by omega
    rw [show (((j - kk P r).toNat : ℕ) : ℤ) = ((j - kk P r).toNat : ℤ) from rfl, e2]; ring
  · rw [if_neg h]
    have hlow : 1 ≤ aa P r j := aa_low_ge_one hP hr j (by omega)
    by_cases h' : j + 1 = kk P r
    · rw [if_pos (by omega)]
      have e : (j + 1 - kk P r).toNat = 0 := by omega
      have e2 : (kk P r - j).toNat = 0 + 1 := by omega
      rw [e, e2, Finset.prod_range_succ]
      simp only [Finset.range_zero, Finset.prod_empty, one_mul, Nat.cast_zero, sub_zero]
      rw [show kk P r - 1 = j by omega]
      field_simp
    · rw [if_neg (by omega)]
      have e2 : (kk P r - j).toNat = (kk P r - (j + 1)).toNat + 1 := by omega
      rw [e2, Finset.prod_range_succ]
      have e3 : kk P r - 1 - (((kk P r - (j + 1)).toNat : ℕ) : ℤ) = j := by omega
      rw [e3]
      have hp := prod_dn_pos hP hr (kk P r - (j + 1)).toNat
      field_simp

lemma wf_nonneg (hP : P.Standing) (hr : 0 < r) (j : ℤ) : 0 ≤ wf P r j := by
  unfold wf
  split_ifs
  · exact Finset.prod_nonneg (fun t _ => aa_nonneg hP hr _)
  · exact div_nonneg zero_le_one (le_trans zero_le_one (prod_dn_pos hP hr _))

lemma wf_kk : wf P r (kk P r) = 1 := by unfold wf; simp

lemma aa_le (hP : P.Standing) (hr : 0 < r) (j : ℤ) :
    aa P r j ≤ P.β * ((mI P r : ℤ) : ℝ) / r := by
  have hβ := hP.1
  unfold aa
  rw [artZ_real]
  apply div_le_div_of_nonneg_right _ hr.le
  apply mul_le_mul_of_nonneg_left _ hβ.le
  have hm : 0 ≤ mI P r := by
    unfold mI; have := hP.2.2.1 r; apply Int.ceil_nonneg; unfold Xstar; positivity
  exact_mod_cast (max_le (min_le_right _ _) hm)

lemma wf_summable (hP : P.Standing) (hr : 0 < r) : Summable (wf P r) := by
  have hβ := hP.1
  have hγ1 : (1 : ℤ) ≤ P.γ := by exact_mod_cast hP.2.1
  set A := P.β * ((mI P r : ℤ) : ℝ) / r with hA
  have hA1 : 1 < A := by
    have := bm_ge hP hr
    have : 0 < P.β * P.f r / r := by have := hP.2.2.1 r; positivity
    linarith
  rw [← (Equiv.addRight (kk P r)).summable_iff]
  apply Summable.of_nat_of_neg
  · -- finite support above
    set T1 : ℕ := (aI P r (kk P r)).toNat with hT1
    refine summable_of_ne_finset_zero (s := Finset.range (T1 + 1)) (fun n hn => ?_)
    have hn' : T1 + 1 ≤ n := by simpa using hn
    show wf P r ((n : ℤ) + kk P r) = 0
    unfold wf
    rw [if_pos (by omega)]
    apply Finset.prod_eq_zero (i := T1) (Finset.mem_range.mpr (by omega))
    unfold aa
    rw [artZ_real]
    have : aI P r (kk P r + T1) ≤ 0 := by
      have e : aI P r (kk P r + T1) = aI P r (kk P r) - (P.γ : ℤ) * T1 := by unfold aI; ring
      have : (T1 : ℤ) ≥ aI P r (kk P r) := by simp only [hT1]; omega
      rw [e]; nlinarith
    rw [max_eq_right (le_trans (min_le_left _ _) this)]; simp
  · -- geometric decay below
    set T0 : ℕ := (mI P r - aI P r (kk P r - 1)).toNat with hT0
    have hlow : ∀ n : ℕ, A ^ (n - T0) ≤ ∏ t ∈ Finset.range n, aa P r (kk P r - 1 - t) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.prod_range_succ]
        have h1 : 1 ≤ aa P r (kk P r - 1 - n) := aa_low_ge_one hP hr _ (by omega)
        have hp0 : 0 ≤ A ^ (n - T0) := by positivity
        by_cases hn : T0 ≤ n
        · have hcap : aa P r (kk P r - 1 - n) = A := by
            rw [aa_dn hP hr _ (aI_low_nonneg hP hr _ (by omega))]
            have : mI P r ≤ aI P r (kk P r - 1 - n) := by
              have e : aI P r (kk P r - 1 - n) = aI P r (kk P r - 1) + (P.γ : ℤ) * n := by
                unfold aI; ring
              rw [e]
              have : (n : ℤ) ≤ (P.γ : ℤ) * n := by nlinarith
              omega
            rw [← lin_id hP hr]
            apply min_eq_right
            apply div_le_div_of_nonneg_right _ hr.le
            apply mul_le_mul_of_nonneg_left _ hβ.le
            exact_mod_cast this
          rw [hcap, show n + 1 - T0 = (n - T0) + 1 by omega, pow_succ]
          exact mul_le_mul_of_nonneg_right ih (by linarith)
        · rw [show n + 1 - T0 = n - T0 by omega]
          have := mul_le_mul ih h1 zero_le_one (le_trans hp0 ih)
          linarith
    have hg : Summable (fun n : ℕ => A ^ T0 * (1 / A) ^ n) :=
      (summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one (by linarith)]; exact hA1)).mul_left _
    refine Summable.of_nonneg_of_le (fun n => wf_nonneg hP hr _) (fun n => ?_) hg
    show wf P r (-(n : ℤ) + kk P r) ≤ _
    unfold wf
    by_cases hn : n = 0
    · subst hn; simp
      exact one_le_pow₀ hA1.le
    rw [if_neg (by omega)]
    rw [show (kk P r - (-(n : ℤ) + kk P r)).toNat = n by omega]
    have hpos : 0 < A ^ (n - T0) := by positivity
    have hp := hlow n
    rw [div_le_iff₀ (lt_of_lt_of_le hpos hp)]
    have : A ^ T0 * (1 / A) ^ n * A ^ (n - T0) ≥ 1 := by
      rw [one_div, inv_pow]
      have hA0 : 0 < A := by linarith
      rcases le_total T0 n with h | h
      · have : A ^ T0 * A ^ (n - T0) = A ^ n := by rw [← pow_add]; congr 1; omega
        rw [mul_comm (A ^ T0), mul_assoc, this, inv_mul_cancel₀ (by positivity)]
      · rw [show n - T0 = 0 by omega, pow_zero, mul_one]
        rw [← div_eq_mul_inv, ge_iff_le, le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ hA1.le h
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ A ^ T0 * (1 / A) ^ n)]

theorem art_exists (hP : P.Standing) (hr : 0 < r) : ∃ q : ℤ → ℝ, IsArtStationary P r q := by
  have hβ := hP.1
  have hs := wf_summable hP hr
  set S := ∑' j, wf P r j with hS
  have hSpos : 0 < S := by
    have := hs.le_tsum (kk P r) (fun j _ => wf_nonneg hP hr j)
    rw [wf_kk] at this; linarith
  have hZle : ∀ j, (artZ P r j : ℝ) ≤ ((mI P r : ℤ) : ℝ) := by
    intro j
    have hm : 0 ≤ mI P r := by
      unfold mI; have := hP.2.2.1 r; apply Int.ceil_nonneg; unfold Xstar; positivity
    rw [artZ_real]; exact_mod_cast (max_le (min_le_right _ _) hm)
  -- detailed balance for the weights
  have hdb : ∀ j, wf P r (j + 1) * r = wf P r j * (P.β * (artZ P r j : ℝ)) := by
    intro j; rw [wf_rec hP hr j]; unfold aa; field_simp
  refine ⟨fun j => wf P r j / S, fun j => div_nonneg (wf_nonneg hP hr j) hSpos.le,
    hs.div_const _, by rw [tsum_div_const]; exact div_self hSpos.ne', ?_, fun j' => ?_⟩
  · refine Summable.of_nonneg_of_le (fun j => mul_nonneg (div_nonneg (wf_nonneg hP hr j) hSpos.le)
      (by unfold artExitRate; positivity)) (fun j => ?_) ((hs.div_const S).mul_right (r + P.β * ((mI P r : ℤ) : ℝ)))
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (wf_nonneg hP hr j) hSpos.le)
    unfold artExitRate
    have := mul_le_mul_of_nonneg_left (hZle j) hβ.le
    linarith
  · have hfun : (fun j => wf P r j / S * artRate P r j j') =
        fun j => (if j = j' + 1 then wf P r (j' + 1) / S * r else 0) +
          (if j = j' - 1 then wf P r (j' - 1) / S * (P.β * (artZ P r (j' - 1) : ℝ)) else 0) := by
      funext j
      simp only [artRate, mul_add]
      congr 1
      · by_cases h1 : j = j' + 1
        · subst h1; simp
        · have : ¬ j' = j - 1 := by omega
          simp [h1, this]
      · by_cases h1 : j = j' - 1
        · subst h1; simp
        · have : ¬ j' = j + 1 := by omega
          simp [h1, this]
    rw [hfun, Summable.tsum_add (summable_of_ne_finset_zero (s := {j' + 1}) (by intro j hj; simp_all))
      (summable_of_ne_finset_zero (s := {j' - 1}) (by intro j hj; simp_all)),
      tsum_ite_eq, tsum_ite_eq]
    have h1 := hdb j'
    have h2 := hdb (j' - 1)
    rw [sub_add_cancel] at h2
    unfold artExitRate
    field_simp
    linarith

end GBSL5

-- ===== part L5fin =====

open Filter Topology MeasureTheory ProbabilityTheory
open RandomLeadGBS.Diffusion

namespace GBSL5
open Real Set
open scoped NNReal
lemma half_mean (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ x, max (-x) 0 ∂(gaussianReal 0 v) = √((v : ℝ) / (2 * π)) := by
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have h1 : ∫ x, gaussianPDFReal 0 v x * max (-x) 0 = ∫ x, gaussianPDFReal 0 v x * max x 0 := by
    rw [← integral_neg_eq_self (fun x => gaussianPDFReal 0 v x * max (-x) 0)]
    congr 1; funext x
    simp only [neg_neg, gaussianPDFReal, sub_zero, even_two, Even.neg_pow]
  rw [h1]
  have h2 : ∫ x, gaussianPDFReal 0 v x * max x 0 =
      ∫ x in Ioi (0 : ℝ), (√(2 * π * v))⁻¹ * (x ^ (1 : ℝ) * rexp (-(1 / (2 * v)) * x ^ (2 : ℝ))) := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; funext x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (mem_Ioi.mpr hx)]
      simp only [gaussianPDFReal, sub_zero, rpow_one, max_eq_left hx.le]
      rw [show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
      have e : -x ^ 2 / (2 * (v : ℝ)) = -(1 / (2 * v)) * x ^ 2 := by ring
      rw [e]; ring
    · rw [indicator_of_notMem (by simpa using hx)]
      simp [max_eq_right (not_lt.mp hx)]
  rw [h2, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by positivity)]
  have e1 : (-((1 : ℝ) + 1) / 2) = -1 := by norm_num
  have e2 : (((1 : ℝ) + 1) / 2) = 1 := by norm_num
  rw [e1, e2, Real.Gamma_one, Real.rpow_neg_one]
  have hπ : 0 < π := Real.pi_pos
  have hs : 0 < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  rw [show ((v : ℝ) / (2 * π)) = ((√(2 * π * v))⁻¹ * v) ^ 2 by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]; field_simp]
  rw [Real.sqrt_sq (by positivity)]
  field_simp



end GBSL5

open GBSL5

theorem solution (P : Params) (hP : P.Standing) :
    (∀ r : ℝ, 0 < r → ∃ p : ℤ → ℝ, IsArtStationary P r p) ∧
    ∀ p : ℝ → ℤ → ℝ, (∀ᶠ r in atTop, IsArtStationary P r (p r)) →
      (∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun r => ∑' j : ℤ, p r j * g (((j : ℝ) - P.xs r) / Real.sqrt r)) atTop
          (𝓝 (∫ x, g x ∂(ProbabilityTheory.gaussianReal 0 (1 / (P.β * P.γ)).toNNReal)))) ∧
      Tendsto (fun r => ∑' j : ℤ, p r j * max (((j : ℝ) - P.xs r) / Real.sqrt r) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) ∧
      Tendsto (fun r => ∑' j : ℤ, p r j * max (-(((j : ℝ) - P.xs r) / Real.sqrt r)) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) := by
  refine ⟨fun r hr => art_exists hP hr, fun p hp => ?_⟩
  set N := gaussianReal 0 (1 / (P.β * P.γ)).toNNReal with hN
  set K : ℝ := (2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)) with hK
  have hβ := hP.1
  have hγr : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have hβγ : 0 < P.β * P.γ := by positivity
  have hπ : 0 < Real.pi := Real.pi_pos
  have hvval : (((1 / (P.β * P.γ)).toNNReal : NNReal) : ℝ) = 1 / (P.β * P.γ) :=
    Real.coe_toNNReal _ (by positivity)
  have hv : (1 / (P.β * P.γ)).toNNReal ≠ 0 := by
    intro h0
    have : (((1 / (P.β * P.γ)).toNNReal : NNReal) : ℝ) = 0 := by rw [h0]; rfl
    rw [hvval] at this
    have : 0 < 1 / (P.β * P.γ) := by positivity
    linarith
  have hNid : Integrable (fun x : ℝ => x) N :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))
  have hnegN : ∫ x, max (-x) 0 ∂N = K := by
    rw [hN, half_mean _ hv, hvval, hK]
    rw [show 1 / (P.β * P.γ) / (2 * Real.pi) = (2 * Real.pi * P.β * P.γ)⁻¹ by field_simp]
    rw [Real.sqrt_inv, Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
  have hmeanN : ∫ x, x ∂N = 0 := by rw [hN, integral_id_gaussianReal]
  have hposN : ∫ x, max x 0 ∂N = K := by
    have e : ∫ x, x ∂N = ∫ x, max x 0 ∂N - ∫ x, max (-x) 0 ∂N := by
      rw [← integral_sub hNid.pos_part hNid.neg_part]
      congr 1; funext x; exact (max_zero_sub_max_neg_zero_eq_self x).symm
    linarith
  refine ⟨fun g => ?_, ?_, ?_⟩
  · refine main_lim hP p hp (fun x => g x) g.continuous ‖g‖ (norm_nonneg _) (fun x => ?_)
      (g.integrable N)
    have := g.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at this
    have : 0 ≤ ‖g‖ * |x| := mul_nonneg (norm_nonneg _) (abs_nonneg _)
    nlinarith
  · rw [← hposN]
    refine main_lim hP p hp (fun x => max x 0) (continuous_id.max continuous_const) 1 zero_le_one
      (fun x => ?_) hNid.pos_part
    rw [abs_of_nonneg (le_max_right _ _)]
    have := le_abs_self x; have := abs_nonneg x
    exact max_le (by linarith) (by linarith)
  · rw [← hnegN]
    refine main_lim hP p hp (fun x => max (-x) 0) (continuous_neg.max continuous_const) 1 zero_le_one
      (fun x => ?_) hNid.neg_part
    rw [abs_of_nonneg (le_max_right _ _)]
    have := neg_le_abs x; have := abs_nonneg x
    exact max_le (by linarith) (by linarith)

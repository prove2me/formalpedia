-- Prove2me | solution 1 for YeIPA.Center.proximity_measures_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T00:03:28.681888+00:00
-- url     : https://prove2.me/submissions/8032ddeb-fac4-444a-b198-da724e2183b7

import Mathlib
import Definitions.Def_YeIPA_Center_AnalyticCenter
import Theorems.Thm_YeIPA_Center_proximity_measures_dominated
import Theorems.Thm_YeIPA_Center_log_sum_bounds

open Matrix

namespace PM100
open YeIPA.Center

variable {m n : ℕ}

theorem K_hasDeriv (sa b : Fin n → ℝ) (hsa : ∀ j, 0 < sa j) :
    HasDerivAt (fun t : ℝ => ∑ j, Real.log (sa j - t * b j)) (∑ j, (-b j) / sa j) 0 := by
  have : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasDerivAt (fun t : ℝ => Real.log (sa j - t * b j)) ((-b j) / sa j) 0 := by
    intro j _
    have h1 : HasDerivAt (fun t : ℝ => sa j - t * b j) (-b j) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (b j)).const_sub (sa j)
    have h2 := h1.log (by simp; exact (hsa j).ne')
    simpa using h2
  have := HasDerivAt.fun_sum this
  simpa using this

theorem kkt (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (ya : Fin m → ℝ) (sa : Fin n → ℝ)
    (hsa : IsAnalyticCenter A c ya sa) : A *ᵥ (fun j => (sa j)⁻¹) = 0 := by
  obtain ⟨⟨hs, hpos⟩, hmax⟩ := hsa
  set v : Fin n → ℝ := fun j => (sa j)⁻¹
  set u := A *ᵥ v
  set b := Aᵀ *ᵥ u
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ j, 0 < sa j - t * b j := by
    rw [Filter.eventually_all]
    intro j
    exact ContinuousAt.eventually_lt continuousAt_const (by fun_prop) (by simpa using hpos j)
  have hloc : IsLocalMax (fun t : ℝ => ∑ j, Real.log (sa j - t * b j)) 0 := by
    filter_upwards [hev] with t ht
    have hslack : slack A c (ya + t • u) = fun j => sa j - t * b j := by
      rw [hs]; funext j
      simp [slack, b, mulVec_add, mulVec_smul]; ring
    have := hmax (ya + t • u) (slack A c (ya + t • u)) ⟨rfl, by rw [hslack]; exact ht⟩
    rw [hslack] at this
    simpa [dualPotential] using this
  have h0 := hloc.hasDerivAt_eq_zero (K_hasDeriv sa b hpos)
  have h1 : b ⬝ᵥ v = 0 := by
    have : ∑ j, (-b j) / sa j = -(b ⬝ᵥ v) := by
      simp [dotProduct, v, div_eq_mul_inv, Finset.sum_neg_distrib]
    linarith
  have h2 : u ⬝ᵥ u = 0 := by
    have : b ⬝ᵥ v = u ⬝ᵥ u := by
      simp only [b, mulVec_transpose]; rw [← dotProduct_mulVec]
    linarith
  exact dotProduct_self_eq_zero.mp h2

theorem K_aux (hn : 0 < n) (z : Fin n → ℝ) (hz : ∀ j, 0 < z j) :
    (∑ j, Real.log (z j / ((∑ k, z k) / n)) =
      ∑ j, Real.log (z j) - (n : ℝ) * Real.log (∑ k, z k) + (n : ℝ) * Real.log n) ∧
    ∑ j, (z j / ((∑ k, z k) / n) - 1) = 0 := by
  have hσ : 0 < ∑ k, z k := Finset.sum_pos (fun j _ => hz j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  constructor
  · have : ∀ j, Real.log (z j / ((∑ k, z k) / n)) =
        Real.log (z j) - Real.log (∑ k, z k) + Real.log n := by
      intro j
      rw [Real.log_div (hz j).ne' (by positivity), Real.log_div hσ.ne' hnr.ne']; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
    ring

theorem amgm (hn : 0 < n) (z : Fin n → ℝ) (hz : ∀ j, 0 < z j) :
    (n : ℝ) * Real.log n ≤ (n : ℝ) * Real.log (∑ j, z j) - ∑ j, Real.log (z j) := by
  obtain ⟨h1, h2⟩ := K_aux hn z hz
  have hσ : 0 < ∑ k, z k := Finset.sum_pos (fun j _ => hz j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have : ∑ j, Real.log (z j / ((∑ k, z k) / n)) ≤ ∑ j, (z j / ((∑ k, z k) / n) - 1) :=
    Finset.sum_le_sum fun j _ => Real.log_le_sub_one_of_pos (by have := hz j; positivity)
  linarith

theorem amgm_eq (hn : 0 < n) (z : Fin n → ℝ) (hz : ∀ j, 0 < z j)
    (h : (n : ℝ) * Real.log (∑ j, z j) - ∑ j, Real.log (z j) = (n : ℝ) * Real.log n) :
    ∀ j, z j = (∑ k, z k) / n := by
  obtain ⟨h1, h2⟩ := K_aux hn z hz
  have hσ : 0 < ∑ k, z k := Finset.sum_pos (fun j _ => hz j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  set μ := (∑ k, z k) / n with hμ
  have hμpos : 0 < μ := by positivity
  have hsum : ∑ j, ((z j / μ - 1) - Real.log (z j / μ)) = 0 := by
    rw [Finset.sum_sub_distrib]; linarith
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (z j / μ - 1) - Real.log (z j / μ) :=
    fun j _ => by
      have := Real.log_le_sub_one_of_pos (show 0 < z j / μ by have := hz j; positivity)
      linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  intro j
  have hj := hall j (Finset.mem_univ _)
  by_contra hne
  have hne' : z j / μ ≠ 1 := by
    intro h'; apply hne; field_simp at h'; linarith
  have := Real.log_lt_sub_one_of_pos (show 0 < z j / μ by have := hz j; positivity) hne'
  linarith

end PM100


open Matrix

namespace PM100
open YeIPA.Center

variable {m n : ℕ}

lemma P2_sum_sq (a : ℝ) (z : Fin n → ℝ) :
    ∑ j, (a * z j - 1) ^ 2 = a ^ 2 * ∑ j, z j ^ 2 - 2 * a * ∑ j, z j + n := by
  have : ∀ j, (a * z j - 1) ^ 2 = a ^ 2 * z j ^ 2 - 2 * a * z j + 1 := fun j => by ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp

lemma P2_identity (N σ E Q : ℝ) (hσ : 0 < σ) (hQ : Q = E + 2 * σ - N) :
    (N / σ) ^ 2 * Q - 2 * (N / σ) * σ + N = N * (N * E - (σ - N) ^ 2) / σ ^ 2 := by
  subst hQ
  field_simp
  ring

lemma P2_ineq (N σ E : ℝ) (hN : 0 < N) (hσ : 0 < σ) (_hE : 0 ≤ E) (hEN : E < N) :
    N * (N * E - (σ - N) ^ 2) / σ ^ 2 ≤ E / (1 - E / N) := by
  have h1 : 1 - E / N = (N - E) / N := by field_simp
  rw [h1, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith [mul_nonneg hN.le (sq_nonneg (E + (σ - N)))]

lemma P2_final (N σ E Q : ℝ) (hN : 0 < N) (hσ : 0 < σ) (hE0 : 0 ≤ E) (hEN : E < N)
    (hQ : Q = E + 2 * σ - N) :
    Real.sqrt ((N / σ) ^ 2 * Q - 2 * (N / σ) * σ + N) ≤
      Real.sqrt E / Real.sqrt (1 - E / N) := by
  rw [← Real.sqrt_div' _ (by rw [sub_nonneg, div_le_one hN]; linarith)]
  apply Real.sqrt_le_sqrt
  rw [P2_identity N σ E Q hσ hQ]
  exact P2_ineq N σ E hN hσ hE0 hEN

/-- (P2) part (ii) of Theorem 3.2. -/
theorem part_ii (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) (s : Fin n → ℝ) (hs : IsDualInterior A c y s)
    (x : Fin n → ℝ) (hx : IsPrimalInterior A x) (h : eta x s < 1) :
    ∃ xh : Fin n → ℝ, (∀ j, 0 ≤ xh j) ∧ A *ᵥ xh = 0 ∧ c ⬝ᵥ xh = n ∧
      s ⬝ᵥ xh = n ∧ eta xh s ≤ eta x s / Real.sqrt (1 - eta x s ^ 2 / n) := by
  obtain ⟨hsc, hspos⟩ := hs
  obtain ⟨hAx, hxpos⟩ := hx
  set σ : ℝ := ∑ j, x j * s j with hσdef
  have hσ : 0 < σ := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun j _ => mul_pos (hxpos j) (hspos j)) Finset.univ_nonempty
  have hsx : s ⬝ᵥ x = σ := by
    simp only [dotProduct, hσdef]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := (n : ℝ) / σ with ht
  have htσ : t * σ = n := by rw [ht]; field_simp
  have ht0 : 0 < t := by positivity
  refine ⟨t • x, fun j => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg ht0.le (hxpos j).le
  · rw [mulVec_smul, hAx, smul_zero]
  · have hc : c = s + Aᵀ *ᵥ y := by rw [hsc, slack]; abel
    rw [hc, add_dotProduct, dotProduct_smul, hsx, smul_eq_mul, htσ, mulVec_transpose,
      ← dotProduct_mulVec, mulVec_smul, hAx, smul_zero, dotProduct_zero, add_zero]
  · rw [dotProduct_smul, hsx, smul_eq_mul, htσ]
  · -- norms
    have hE0 : 0 ≤ ∑ j, (x j * s j - 1) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have heta : eta x s = Real.sqrt (∑ j, (x j * s j - 1) ^ 2) := rfl
    have heta2 : eta x s ^ 2 = ∑ j, (x j * s j - 1) ^ 2 := by
      rw [heta, Real.sq_sqrt hE0]
    have hEN : ∑ j, (x j * s j - 1) ^ 2 < (n : ℝ) := by
      have h1 : eta x s ^ 2 < 1 := by
        have : 0 ≤ eta x s := Real.sqrt_nonneg _
        nlinarith
      have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hQ : ∑ j, (x j * s j) ^ 2 = (∑ j, (x j * s j - 1) ^ 2) + 2 * σ - (n : ℝ) := by
      have := P2_sum_sq 1 (fun j => x j * s j)
      simp only [one_mul, one_pow] at this
      rw [this, hσdef]; ring
    have hxh : eta (t • x) s = Real.sqrt (∑ j, (t * (x j * s j) - 1) ^ 2) := by
      simp only [eta, norm2, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [hxh, P2_sum_sq t (fun j => x j * s j), ← hσdef, heta2, heta]
    exact P2_final n σ _ _ hN hσ hE0 hEN hQ

end PM100


open Matrix

namespace PM100
open YeIPA.Center

variable {m n : ℕ}

theorem norm2_sq (v : Fin n → ℝ) : norm2 v ^ 2 = ∑ j, v j ^ 2 := by
  unfold norm2
  exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem norm2_nonneg (v : Fin n → ℝ) : 0 ≤ norm2 v := Real.sqrt_nonneg _

theorem abs_le_norm2 (v : Fin n → ℝ) (j : Fin n) : |v j| ≤ norm2 v := by
  unfold norm2
  rw [Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _), sq_abs]
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)

theorem normInf_le (hn : 0 < n) (v : Fin n → ℝ) : normInf v ≤ norm2 v := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ciSup_le fun j => abs_le_norm2 v j

theorem cs (d w : Fin n → ℝ) : |∑ j, d j * w j| ≤ norm2 d * norm2 w := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ d w
  rw [← norm2_sq, ← norm2_sq, ← mul_pow] at h
  exact abs_le_of_sq_le_sq' h (mul_nonneg (norm2_nonneg d) (norm2_nonneg w)) |> fun h' =>
    abs_le.mpr ⟨h'.1, h'.2⟩

/-- `c ⬝ x = s ⬝ x` for primal interior `x` and dual interior `(y, s)`. -/
theorem cx_eq (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (hs : s = slack A c y) (x : Fin n → ℝ) (hx : A *ᵥ x = 0) : c ⬝ᵥ x = s ⬝ᵥ x := by
  rw [hs, slack, sub_dotProduct, dotProduct_comm (Aᵀ *ᵥ y), dotProduct_mulVec, vecMul_transpose, hx]
  simp

theorem P_eq (c x s : Fin n → ℝ) (hcx : c ⬝ᵥ x = s ⬝ᵥ x) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) :
    primalPotential c x = pdPotential x s + dualPotential s := by
  unfold primalPotential pdPotential dualPotential
  rw [hcx, dotProduct_comm]
  have : ∀ j, Real.log (x j * s j) = Real.log (x j) + Real.log (s j) :=
    fun j => Real.log_mul (hx j).ne' (hs j).ne'
  simp only [this, Finset.sum_add_distrib]
  ring

theorem psi_bound (hn : 0 < n) (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (h : eta x s < 1) :
    pdPotential x s - (n : ℝ) * Real.log n ≤ eta x s ^ 2 / (2 * (1 - eta x s)) := by
  set d : Fin n → ℝ := fun j => x j * s j - 1 with hd
  set η := eta x s with hη
  have hηd : norm2 d = η := rfl
  have hinf : normInf d ≤ η := hηd ▸ normInf_le hn d
  have hz : ∀ j, 1 + d j = x j * s j := fun j => by simp [hd]
  have hlsb := log_sum_bounds d (lt_of_le_of_lt hinf h)
  have hsum : x ⬝ᵥ s = n + ∑ j, d j := by
    simp only [dotProduct, hd, Finset.sum_sub_distrib]
    simp
  have hpos : 0 < x ⬝ᵥ s := Finset.sum_pos (fun j _ => mul_pos (hx j) (hs j)) ⟨⟨0, hn⟩, by simp⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog1 : Real.log (x ⬝ᵥ s) ≤ Real.log n + (∑ j, d j) / n := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hpos hnpos)
    rw [Real.log_div hpos.ne' hnpos.ne', hsum] at h1
    rw [hsum]
    have : (↑n + ∑ j, d j) / ↑n - 1 = (∑ j, d j) / n := by field_simp; ring
    linarith
  have hpd : pdPotential x s = (n : ℝ) * Real.log (x ⬝ᵥ s) - ∑ j, Real.log (1 + d j) := by
    unfold pdPotential; simp only [hz]
  have hk : norm2 d ^ 2 / (2 * (1 - normInf d)) ≤ η ^ 2 / (2 * (1 - η)) := by
    rw [hηd]
    have hη0 : 0 ≤ η := norm2_nonneg d
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  have hmul : (n : ℝ) * Real.log (x ⬝ᵥ s) ≤ n * Real.log n + ∑ j, d j := by
    have := mul_le_mul_of_nonneg_left hlog1 hnpos.le
    rw [mul_add, mul_div_cancel₀ _ hnpos.ne'] at this
    exact this
  rw [hpd]
  linarith [hlsb.2]

/-- the core estimate for part (iv) -/
theorem core (hn : 0 < n) (x s u : Fin n → ℝ) (hu : ∀ j, 0 < u j) (h : eta x s < 1)
    (hrel : ∑ j, (u j)⁻¹ + ∑ j, x j * s j * u j = n + ∑ j, x j * s j) :
    norm2 (fun j => u j - 1) ≤ eta x s / (1 - eta x s) := by
  set d : Fin n → ℝ := fun j => x j * s j - 1 with hd
  set w : Fin n → ℝ := fun j => u j - 1 with hw
  set η := eta x s with hη
  have hηd : norm2 d = η := rfl
  set W := norm2 w with hW
  have hW0 : 0 ≤ W := norm2_nonneg w
  have hη0 : 0 ≤ η := norm2_nonneg d
  have hid : ∑ j, w j ^ 2 / u j = -∑ j, d j * w j := by
    have e1 : ∀ j, w j ^ 2 / u j = u j + (u j)⁻¹ - 2 := by
      intro j; have := (hu j).ne'; simp only [hw]; field_simp; ring
    have e2 : ∀ j, d j * w j = x j * s j * u j - x j * s j - u j + 1 := by
      intro j; simp only [hd, hw]; ring
    simp only [e1, e2, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hlow : W ^ 2 / (1 + W) ≤ ∑ j, w j ^ 2 / u j := by
    rw [hW, norm2_sq, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    have hu1 : u j ≤ 1 + norm2 w := by
      have := abs_le_norm2 w j
      have := le_abs_self (w j)
      simp only [hw] at *
      linarith
    exact div_le_div_of_nonneg_left (sq_nonneg _) (hu j) hu1
  have hup : -∑ j, d j * w j ≤ η * W := by
    have := cs d w
    rw [hηd] at this
    linarith [neg_abs_le (∑ j, d j * w j)]
  have key : W ^ 2 ≤ η * W * (1 + W) := by
    have h1 : W ^ 2 / (1 + W) ≤ η * W := by linarith
    rwa [div_le_iff₀ (by linarith)] at h1
  have key2 : W ≤ η * (1 + W) := by
    rcases eq_or_lt_of_le hW0 with h0 | h0
    · rw [← h0]; positivity
    · nlinarith
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem main {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (hA : StandingAssumptions A c)
    (y : Fin m → ℝ) (s : Fin n → ℝ) (hs : IsDualInterior A c y s)
    (ya : Fin m → ℝ) (sa : Fin n → ℝ) (hsa : IsAnalyticCenter A c ya sa)
    (x : Fin n → ℝ) (hx : IsPrimalInterior A x)
    (xa : Fin n → ℝ) (hxa : IsPrimalPotentialMinimizer A c xa) :
    (etaD A s ≤ eta x s ∧ etaP A c x ≤ eta x s ∧
      (etaD A s < 1 → ∃ x' : Fin n → ℝ, IsPrimalInterior A x' ∧ eta x' s ≤ etaD A s) ∧
      (etaP A c x < 1 → ∃ (y' : Fin m → ℝ) (s' : Fin n → ℝ),
        IsDualInterior A c y' s' ∧ eta x s' ≤ etaP A c x)) ∧
    (eta x s < 1 → ∃ xh : Fin n → ℝ, (∀ j, 0 ≤ xh j) ∧ A *ᵥ xh = 0 ∧ c ⬝ᵥ xh = n ∧
      s ⬝ᵥ xh = n ∧ eta xh s ≤ eta x s / Real.sqrt (1 - eta x s ^ 2 / n)) ∧
    (eta x s < 1 → c ⬝ᵥ x = n →
      pdPotential x s - pdPotential xa sa ≤ eta x s ^ 2 / (2 * (1 - eta x s)) ∧
      primalPotential c x - primalPotential c xa ≤ eta x s ^ 2 / (2 * (1 - eta x s)) ∧
      dualPotential sa - dualPotential s ≤ eta x s ^ 2 / (2 * (1 - eta x s))) ∧
    (eta x s < 1 →
      norm2 (fun j => sa j / s j - 1) ≤ eta x s / (1 - eta x s) ∧
      norm2 (fun j => xa j / x j - 1) ≤ eta x s / (1 - eta x s)) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hA.2.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- analytic center facts
  set xb : Fin n → ℝ := fun j => (sa j)⁻¹ with hxb
  have hsa0 := hsa.1.2
  have hxb0 : ∀ j, 0 < xb j := fun j => inv_pos.mpr (hsa0 j)
  have hAxb : A *ᵥ xb = 0 := kkt A c ya sa hsa
  have hsaxb : sa ⬝ᵥ xb = n := by
    simp [dotProduct, hxb, mul_inv_cancel₀ (hsa0 _).ne']
  have hcxb : c ⬝ᵥ xb = n := by rw [cx_eq A c ya sa hsa.1.1 xb hAxb, hsaxb]
  have hPxb : primalPotential c xb = n * Real.log n + dualPotential sa := by
    rw [P_eq c xb sa (cx_eq A c ya sa hsa.1.1 xb hAxb) hxb0 hsa0]
    congr 1
    unfold pdPotential
    rw [dotProduct_comm, hsaxb]
    simp [hxb, mul_inv_cancel₀ (hsa0 _).ne', inv_mul_cancel₀ (hsa0 _).ne']
  have hxa0 := hxa.1.2
  have hcxa : c ⬝ᵥ xa = s ⬝ᵥ xa := cx_eq A c y s hs.1 xa hxa.1.1
  have hcxa' : c ⬝ᵥ xa = sa ⬝ᵥ xa := cx_eq A c ya sa hsa.1.1 xa hxa.1.1
  have hPxa : primalPotential c xa = pdPotential xa sa + dualPotential sa :=
    P_eq c xa sa hcxa' hxa0 hsa0
  have hpd_ge : (n : ℝ) * Real.log n ≤ pdPotential xa sa := by
    have := amgm hn (fun j => xa j * sa j) (fun j => mul_pos (hxa0 j) (hsa0 j))
    simpa [pdPotential, dotProduct] using this
  have hPmin : primalPotential c xa ≤ primalPotential c xb := hxa.2.2 xb ⟨hAxb, hxb0⟩
  have hpd_eq : pdPotential xa sa = n * Real.log n := by linarith
  have hprod : ∀ j, xa j * sa j = 1 := by
    have h := amgm_eq hn (fun j => xa j * sa j) (fun j => mul_pos (hxa0 j) (hsa0 j))
      (by simpa [pdPotential, dotProduct] using hpd_eq)
    intro j
    rw [h j]
    have : ∑ k, xa k * sa k = n := by
      rw [← hxa.2.1, hcxa', dotProduct_comm]; rfl
    rw [this, div_self hnpos.ne']
  have hB : dualPotential s ≤ dualPotential sa := hsa.2 y s hs
  have hPxx : primalPotential c xa ≤ primalPotential c x := hxa.2.2 x hx
  have hcx : c ⬝ᵥ x = s ⬝ᵥ x := cx_eq A c y s hs.1 x hx.1
  have hPx : primalPotential c x = pdPotential x s + dualPotential s := P_eq c x s hcx hx.2 hs.2
  refine ⟨proximity_measures_dominated A c hA y s hs x hx, fun h => part_ii hn A c y s hs x hx h,
    fun h _ => ?_, fun h => ⟨?_, ?_⟩⟩
  · have hψ := psi_bound hn x s hx.2 hs.2 h
    refine ⟨by linarith, by linarith, by linarith⟩
  · have := core hn x s (fun j => sa j / s j) (fun j => div_pos (hsa0 j) (hs.2 j)) h ?_
    · exact this
    have e1 : ∑ j, (sa j / s j)⁻¹ = n := by
      have : ∑ j, (sa j / s j)⁻¹ = s ⬝ᵥ xb := by
        simp [dotProduct, hxb, div_eq_mul_inv, mul_comm]
      rw [this, ← cx_eq A c y s hs.1 xb hAxb, hcxb]
    have e2 : ∑ j, x j * s j * (sa j / s j) = ∑ j, x j * s j := by
      have h1 : ∑ j, x j * s j * (sa j / s j) = sa ⬝ᵥ x := by
        simp only [dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp [(hs.2 j).ne']
      have h2 : ∑ j, x j * s j = s ⬝ᵥ x := by
        simp only [dotProduct]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [h1, h2, ← cx_eq A c ya sa hsa.1.1 x hx.1, hcx]
    rw [e1, e2]
  · have := core hn x s (fun j => xa j / x j) (fun j => div_pos (hxa0 j) (hx.2 j)) h ?_
    · exact this
    have e1 : ∑ j, (xa j / x j)⁻¹ = ∑ j, x j * s j := by
      have h1 : ∑ j, (xa j / x j)⁻¹ = sa ⬝ᵥ x := by
        simp only [dotProduct, inv_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hsj : sa j = (xa j)⁻¹ := eq_inv_of_mul_eq_one_right (hprod j)
        rw [div_eq_mul_inv, hsj]; ring
      have h2 : ∑ j, x j * s j = s ⬝ᵥ x := by
        simp only [dotProduct]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [h1, h2, ← cx_eq A c ya sa hsa.1.1 x hx.1, hcx]
    have e2 : ∑ j, x j * s j * (xa j / x j) = n := by
      have h1 : ∑ j, x j * s j * (xa j / x j) = s ⬝ᵥ xa := by
        simp only [dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp [(hx.2 j).ne']
      rw [h1, ← hcxa, hxa.2.1]
    rw [e1, e2]; ring

end PM100

open Matrix
open YeIPA.Center

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (hA : StandingAssumptions A c)
    (y : Fin m → ℝ) (s : Fin n → ℝ) (hs : IsDualInterior A c y s)
    (ya : Fin m → ℝ) (sa : Fin n → ℝ) (hsa : IsAnalyticCenter A c ya sa)
    (x : Fin n → ℝ) (hx : IsPrimalInterior A x)
    (xa : Fin n → ℝ) (hxa : IsPrimalPotentialMinimizer A c xa) :
    -- (i)
    (etaD A s ≤ eta x s ∧ etaP A c x ≤ eta x s ∧
      (etaD A s < 1 → ∃ x' : Fin n → ℝ, IsPrimalInterior A x' ∧ eta x' s ≤ etaD A s) ∧
      (etaP A c x < 1 → ∃ (y' : Fin m → ℝ) (s' : Fin n → ℝ),
        IsDualInterior A c y' s' ∧ eta x s' ≤ etaP A c x)) ∧
    -- (ii)
    (eta x s < 1 → ∃ xh : Fin n → ℝ, (∀ j, 0 ≤ xh j) ∧ A *ᵥ xh = 0 ∧ c ⬝ᵥ xh = n ∧
      s ⬝ᵥ xh = n ∧ eta xh s ≤ eta x s / Real.sqrt (1 - eta x s ^ 2 / n)) ∧
    -- (iii)
    (eta x s < 1 → c ⬝ᵥ x = n →
      pdPotential x s - pdPotential xa sa ≤ eta x s ^ 2 / (2 * (1 - eta x s)) ∧
      primalPotential c x - primalPotential c xa ≤ eta x s ^ 2 / (2 * (1 - eta x s)) ∧
      dualPotential sa - dualPotential s ≤ eta x s ^ 2 / (2 * (1 - eta x s))) ∧
    -- (iv)
    (eta x s < 1 →
      norm2 (fun j => sa j / s j - 1) ≤ eta x s / (1 - eta x s) ∧
      norm2 (fun j => xa j / x j - 1) ≤ eta x s / (1 - eta x s)) :=
  PM100.main A c hA y s hs ya sa hsa x hx xa hxa

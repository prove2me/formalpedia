-- Prove2me | solution 2 for QAlgorithms.DeWolf.shor_periodFinding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:57:32.021965+00:00
-- url     : https://prove2.me/submissions/508c694e-375f-41db-b094-771f99ea71f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Theorems.Thm_QAlgorithms_DeWolf_shor_good_probability_totient
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_pointwise

set_option autoImplicit false

private lemma rational_unique (N q r c b : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hNq : N ^ 2 < q)
    (hb : |(b : ℝ) / q - (c : ℝ) / r| ≤ 1 / (2 * (q : ℝ)))
    (p : ℤ) (s : ℕ) (hs : 1 ≤ s) (hsN : s ≤ N)
    (hp : |(b : ℝ) / q - (p : ℝ) / s| ≤ 1 / (2 * (q : ℝ))) :
    (p : ℝ) / s = (c : ℝ) / r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hprod : (r : ℝ) * s < q := by
    have hnat : r * s ≤ N ^ 2 := by nlinarith
    exact_mod_cast hnat.trans_lt hNq
  have hdist : |(p : ℝ) / s - (c : ℝ) / r| ≤ 1 / q := by
    calc
      _ ≤ |(p : ℝ) / s - (b : ℝ) / q| + |(b : ℝ) / q - (c : ℝ) / r| := abs_sub_le _ _ _
      _ ≤ 1 / (2 * (q : ℝ)) + 1 / (2 * (q : ℝ)) := add_le_add (by rwa [abs_sub_comm]) hb
      _ = 1 / q := by ring
  have heq : ((p * r - (c : ℤ) * s : ℤ) : ℝ) =
      ((p : ℝ) / s - (c : ℝ) / r) * ((r : ℝ) * s) := by
    push_cast
    field_simp
  have hsmall : |((p * r - (c : ℤ) * s : ℤ) : ℝ)| < 1 := by
    rw [heq, abs_mul, abs_of_pos (mul_pos hr0 hs0)]
    calc
      _ ≤ (1 / (q : ℝ)) * ((r : ℝ) * s) := mul_le_mul_of_nonneg_right hdist (by positivity)
      _ = ((r : ℝ) * s) / q := by ring
      _ < 1 := (div_lt_one hq0).2 hprod
  have hz : p * (r : ℤ) - (c : ℤ) * s = 0 := by
    have : |p * (r : ℤ) - (c : ℤ) * s| < (1 : ℤ) := by exact_mod_cast hsmall
    have hnonneg := abs_nonneg (p * (r : ℤ) - (c : ℤ) * s)
    exact abs_eq_zero.mp (by omega : |p * (r : ℤ) - (c : ℤ) * s| = 0)
  apply (div_eq_div_iff hs0.ne' hr0.ne').2
  exact_mod_cast (sub_eq_zero.mp hz)

private lemma reduced_den (r c : ℕ) (hr : 1 ≤ r) (hc : Nat.Coprime c r) :
    ((c : ℚ) / r).den = r := by
  have h := Rat.den_div_eq_of_coprime (a := (c : ℤ)) (b := (r : ℤ))
    (by exact_mod_cast hr) (by simpa using hc)
  simpa using h

private lemma loglog_lower (R : ℕ) (hR : Real.exp (Real.exp 1) ≤ (R : ℝ))
    (n : ℕ) (hn : R ≤ n) : 1 ≤ Real.log (Real.log (n : ℝ)) := by
  have hx : Real.exp (Real.exp 1) ≤ (n : ℝ) := hR.trans (by exact_mod_cast hn)
  have hlog : Real.exp 1 ≤ Real.log (n : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos _) hx
  simpa using Real.log_le_log (Real.exp_pos 1) hlog

private lemma uniform_totient_lower
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRS : ∀ r : ℕ, 3 ≤ r → (r : ℝ) / Nat.totient r <
      A * Real.log (Real.log (r : ℝ)) + B / Real.log (Real.log (r : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ N →
        c / Real.log (Real.log (N : ℝ)) ≤ (Nat.totient r : ℝ) / r := by
  let R : ℕ := max 3 ⌈Real.exp (Real.exp 1)⌉₊
  have hR3 : 3 ≤ R := le_max_left _ _
  have hR : Real.exp (Real.exp 1) ≤ (R : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 3 ⌈Real.exp (Real.exp 1)⌉₊))
  let M : ℝ := (R : ℝ) + A + B + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨1 / M, by positivity, R, ?_⟩
  intro N hN r hr hrN
  have hllN : 1 ≤ Real.log (Real.log (N : ℝ)) := loglog_lower R hR N hN
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hphi : (1 : ℝ) ≤ Nat.totient r := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < r by omega)
  have hrat : (r : ℝ) / Nat.totient r ≤ M * Real.log (Real.log (N : ℝ)) := by
    by_cases hrR : r < R
    · calc
        _ ≤ (r : ℝ) := div_le_self hr0.le hphi
        _ ≤ (R : ℝ) := by exact_mod_cast hrR.le
        _ ≤ M := by dsimp [M]; linarith
        _ ≤ M * Real.log (Real.log (N : ℝ)) := le_mul_of_one_le_right hM.le hllN
    · have hRr : R ≤ r := by omega
      have hllr : 1 ≤ Real.log (Real.log (r : ℝ)) := loglog_lower R hR r hRr
      have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
      have hmono : Real.log (Real.log (r : ℝ)) ≤ Real.log (Real.log (N : ℝ)) :=
        Real.log_le_log hlogr (Real.log_le_log hr0 (by exact_mod_cast hrN))
      calc
        _ ≤ A * Real.log (Real.log (r : ℝ)) + B / Real.log (Real.log (r : ℝ)) :=
          (hRS r (hR3.trans hRr)).le
        _ ≤ A * Real.log (Real.log (N : ℝ)) + B :=
          add_le_add (mul_le_mul_of_nonneg_left hmono hA) (div_le_self hB hllr)
        _ ≤ (A + B) * Real.log (Real.log (N : ℝ)) := by nlinarith
        _ ≤ M * Real.log (Real.log (N : ℝ)) := by dsimp [M]; nlinarith
  have hmul : (r : ℝ) ≤ (M * Real.log (Real.log (N : ℝ))) * Nat.totient r :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < Nat.totient r)).1 hrat
  apply (le_div_iff₀ hr0).2
  calc
    _ = (r : ℝ) / (M * Real.log (Real.log (N : ℝ))) := by ring
    _ ≤ Nat.totient r := (div_le_iff₀ (mul_pos hM (by positivity))).2 (by nlinarith)

open QAlgorithms QAlgorithms.DeWolf

theorem solution :
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → r ≤ N →
      ∀ f : ℕ → ℕ, (∀ a, f a < N) → HasPeriod f r →
        C / Real.log (Real.log N) ≤ probEvent (shorRunState N f) fun z =>
          ∃ c : ℕ, c < r ∧ Nat.Coprime c r ∧
            |(bitsToNat z.1 : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤
              1 / (2 * (2 : ℝ) ^ shorEll N)) ∧
    (∀ N r c b : ℕ, 1 ≤ r → r ≤ N → c < r → Nat.Coprime c r →
      |(b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
        ((c : ℚ) / r).den = r ∧
        ∀ (p : ℤ) (s : ℕ), 1 ≤ s → s ≤ N →
          |(b : ℝ) / (2 : ℝ) ^ shorEll N - (p : ℝ) / s| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
            (p : ℝ) / s = (c : ℝ) / r) := by
  constructor
  · obtain ⟨a, ha, N₁, hquantum⟩ := shor_good_probability_totient
    obtain ⟨c, hc, N₂, htotient⟩ := uniform_totient_lower
      (Real.exp Real.eulerMascheroniConstant) 2.50637
      (Real.exp_pos _).le (by norm_num)
      TaoFivePrimes.rosser_schoenfeld_totient_pointwise
    refine ⟨a * c, mul_pos ha hc, max N₁ N₂, ?_⟩
    intro N hN r hr hrN f hf hperiod
    calc
      (a * c) / Real.log (Real.log (N : ℝ)) =
          a * (c / Real.log (Real.log (N : ℝ))) := by ring
      _ ≤ a * ((Nat.totient r : ℝ) / r) :=
        mul_le_mul_of_nonneg_left
          (htotient N ((le_max_right _ _).trans hN) r hr hrN) ha.le
      _ ≤ _ := hquantum N ((le_max_left _ _).trans hN) r hr hrN f hf hperiod
  · intro N r c b hr hrN hcr hcop hb
    refine ⟨reduced_den r c hr hcop, ?_⟩
    intro p s hs hsN hp
    have hq : N ^ 2 < 2 ^ shorEll N := by
      have := Nat.le_pow_clog (by decide : 1 < 2) (N ^ 2 + 1)
      change N ^ 2 < 2 ^ Nat.clog 2 (N ^ 2 + 1)
      omega
    convert rational_unique N (2 ^ shorEll N) r c b hr hrN hq ?_ p s hs hsN ?_ using 1 <;>
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using (show _ from by assumption)

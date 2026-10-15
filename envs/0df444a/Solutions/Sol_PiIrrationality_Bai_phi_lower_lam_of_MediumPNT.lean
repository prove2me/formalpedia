-- Prove2me | solution 1 for PiIrrationality.Bai.phi_lower_lam_of_MediumPNT
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T20:09:30.566981+00:00
-- url     : https://prove2.me/submissions/8df78dfc-eed8-4b09-8d60-222f297aafb4

import Definitions.Def_PiIrrationality_BaiForms
import Mathlib.Tactic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false

namespace PiIrrationality.BaiPhi
open PiIrrationality.Bai (Dd okRow chainOk term)

open Finset

lemma Dd_eq : Dd = 7685213070 := rfl

variable {L : List (ℕ × ℕ × ℕ × ℕ × ℕ)}

lemma row_facts (hL : L.all okRow = true) (t : ℕ × ℕ × ℕ × ℕ × ℕ) (ht : t ∈ L) :
    t.1 < t.2.1 ∧ t.2.1 ≤ Dd ∧ Dd ≤ 7430 * t.1 ∧
    2 * t.2.2.1 * Dd ≤ 2 * 1857 * t.1 + Dd ∧ 2 * 1857 * t.2.1 + Dd ≤ 2 * (t.2.2.1 + 1) * Dd ∧
    t.2.2.2.1 * Dd ≤ 3714 * t.1 ∧ 3714 * t.2.1 ≤ (t.2.2.2.1 + 1) * Dd ∧
    t.2.2.2.2 * Dd ≤ 5570 * t.1 ∧ 5570 * t.2.1 ≤ (t.2.2.2.2 + 1) * Dd ∧
    2 * 3715 * t.2.1 + Dd + 2 * t.2.2.2.2 * Dd ≤ 2 * t.2.2.1 * Dd + 4 * t.2.2.2.1 * Dd := by
  have h := List.all_eq_true.1 hL t ht
  simp only [okRow, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

lemma row_A_pos (hL : L.all okRow = true) (t : ℕ × ℕ × ℕ × ℕ × ℕ) (ht : t ∈ L) : 0 < t.1 := by
  have h := (row_facts hL t ht).2.2.1
  rw [Dd_eq] at h
  omega

end PiIrrationality.BaiPhi

section
namespace PiIrrationality.BaiPhi
open PiIrrationality.Bai (Dd okRow chainOk term)
variable {L : List (ℕ × ℕ × ℕ × ℕ × ℕ)}

open Finset Filter Asymptotics

/-! ## Prime intervals, membership in Bai's deleted set, disjointness -/

/-- Primes `p` with `(mD+A) p ≤ nD < (mD+B) p`, i.e. `m + A/D ≤ n/p < m + B/D`. -/
def Iset (n m : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ) : Finset ℕ :=
  (range (n * Dd + 1)).filter fun p => p.Prime ∧ (m * Dd + t.1) * p ≤ n * Dd ∧ n * Dd < (m * Dd + t.2.1) * p

lemma mem_deleted (hL : L.all okRow = true) (K n m p : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ) (ht : t ∈ L) (hm : m < K)
    (hn : 7430 * K ^ 2 ≤ n) (hp : p ∈ Iset n m t) : p ∈ PiIrrationality.Bai.deletedPrimes n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := row_facts hL t ht
  simp only [Iset, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨-, hpp, hlo, hhi⟩ := hp
  have hp0 : 0 < p := hpp.pos
  have hK1 : 1 ≤ K := by omega
  rw [Dd_eq] at h2 h3 h4 h5 h6 h7 h8 h9 h10 hlo hhi
  have hnK : n < K * p := by
    have h' : n * 7685213070 < (K * p) * 7685213070 := by
      calc n * 7685213070 < (m * 7685213070 + t.2.1) * p := hhi
        _ ≤ (K * 7685213070) * p := by
          apply Nat.mul_le_mul_right
          calc m * 7685213070 + t.2.1 ≤ m * 7685213070 + 7685213070 := Nat.add_le_add_left h2 _
            _ = (m + 1) * 7685213070 := by ring
            _ ≤ K * 7685213070 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hm)
        _ = (K * p) * 7685213070 := by ring
    exact Nat.lt_of_mul_lt_mul_right h'
  simp only [PiIrrationality.Bai.deletedPrimes, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hpp, ?_, ?_, ?_⟩
  · have : 7685213070 * p ≤ 7685213070 * (7430 * n) := by
      calc 7685213070 * p ≤ (7430 * t.1) * p := Nat.mul_le_mul_right _ h3
        _ ≤ 7430 * ((m * 7685213070 + t.1) * p) := by
          rw [mul_assoc]; apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_right; omega
        _ ≤ 7430 * (n * 7685213070) := Nat.mul_le_mul_left _ hlo
        _ = 7685213070 * (7430 * n) := by ring
    omega
  · have h5K : K * 5 < K * p := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left h5K
  · have hsq : n * n < (K * p) * (K * p) := Nat.mul_self_lt_mul_self hnK
    have hnn : 7430 * K ^ 2 * n ≤ n * n := Nat.mul_le_mul_right n hn
    have : K ^ 2 * (7430 * n) < K ^ 2 * p ^ 2 := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  · have hp' : (0 : ℚ) < p := by exact_mod_cast hp0
    have hlo' : (m : ℚ) * 7685213070 + t.1 ≤ (n : ℚ) / p * 7685213070 := by
      have : (((m * 7685213070 + t.1) * p : ℕ) : ℚ) ≤ ((n * 7685213070 : ℕ) : ℚ) := by exact_mod_cast hlo
      push_cast at this
      rw [div_mul_eq_mul_div, le_div_iff₀ hp']; linarith
    have hhi' : (n : ℚ) / p * 7685213070 < (m : ℚ) * 7685213070 + t.2.1 := by
      have : ((n * 7685213070 : ℕ) : ℚ) < (((m * 7685213070 + t.2.1) * p : ℕ) : ℚ) := by exact_mod_cast hhi
      push_cast at this
      rw [div_mul_eq_mul_div, div_lt_iff₀ hp']; linarith
    have q4 : (2 * t.2.2.1 * 7685213070 : ℚ) ≤ 2 * 1857 * t.1 + 7685213070 := by exact_mod_cast h4
    have q5 : (2 * 1857 * t.2.1 + 7685213070 : ℚ) ≤ 2 * (t.2.2.1 + 1) * 7685213070 := by exact_mod_cast h5
    have q6 : (t.2.2.2.1 * 7685213070 : ℚ) ≤ 3714 * t.1 := by exact_mod_cast h6
    have q7 : (3714 * t.2.1 : ℚ) ≤ (t.2.2.2.1 + 1) * 7685213070 := by exact_mod_cast h7
    have q8 : (t.2.2.2.2 * 7685213070 : ℚ) ≤ 5570 * t.1 := by exact_mod_cast h8
    have q9 : (5570 * t.2.1 : ℚ) ≤ (t.2.2.2.2 + 1) * 7685213070 := by exact_mod_cast h9
    have q10 : (2 * 3715 * t.2.1 + 7685213070 + 2 * t.2.2.2.2 * 7685213070 : ℚ) ≤
        2 * t.2.2.1 * 7685213070 + 4 * t.2.2.2.1 * 7685213070 := by exact_mod_cast h10
    have e1 : Int.fract (((1857 * n : ℕ) : ℚ) / p + 1 / 2) =
        1857 * ((n : ℚ) / p) + 1 / 2 - (1857 * m + t.2.2.1) := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 1857 * m + t.2.2.1, ?_⟩
      push_cast; ring
    have e2 : Int.fract (((3714 * n : ℕ) : ℚ) / p) = 3714 * ((n : ℚ) / p) - (3714 * m + t.2.2.2.1) := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 3714 * m + t.2.2.2.1, ?_⟩
      push_cast; ring
    have e3 : Int.fract (((5570 * n : ℕ) : ℚ) / p) = 5570 * ((n : ℚ) / p) - (5570 * m + t.2.2.2.2) := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 5570 * m + t.2.2.2.2, ?_⟩
      push_cast; ring
    rw [e1, e2, e3]
    linarith

lemma chain_pairwise (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (hc : chainOk l = true)
    (hl : ∀ t ∈ l, t.1 < t.2.1) : l.Pairwise (fun x y => x.2.1 ≤ y.1) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x rest ih =>
    cases rest with
    | nil => exact List.pairwise_singleton _ _
    | cons y rest' =>
      simp only [chainOk, Bool.and_eq_true, Nat.ble_eq] at hc
      have ih' := ih hc.2 (fun t ht => hl t (List.mem_cons_of_mem _ ht))
      rw [List.pairwise_cons]
      refine ⟨?_, ih'⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz'
      · exact hc.1
      · have hyz := (List.pairwise_cons.1 ih').1 z hz'
        have hy := hl y (by simp)
        omega

lemma rows_pairwise (hL : L.all okRow = true) (hc : chainOk L = true) :
    L.Pairwise (fun x y => x.2.1 ≤ y.1) :=
  chain_pairwise L hc (fun t ht => (row_facts hL t ht).1)

lemma rows_nodup (hL : L.all okRow = true) (hc : chainOk L = true) : L.Nodup := by
  apply (rows_pairwise hL hc).imp_of_mem
  intro a b ha _ hab heq
  subst heq
  have := (row_facts hL a ha).1
  omega

lemma pairwise_or {α : Type} {R : α → α → Prop} (l : List α) (h : l.Pairwise R) :
    ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b ∨ R b a := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.pairwise_cons] at h
    intro a ha b hb hab
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact Or.inl (h.1 b hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact Or.inr (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

lemma Iset_disjoint (hL : L.all okRow = true) (hc : chainOk L = true)
    (n : ℕ) (i j : ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ)) (hi : i.2 ∈ L) (hj : j.2 ∈ L)
    (hij : i ≠ j) : Disjoint (Iset n i.1 i.2) (Iset n j.1 j.2) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [Iset, Finset.mem_filter, Finset.mem_range] at hp1 hp2
  obtain ⟨-, hpp, a1, b1⟩ := hp1
  obtain ⟨-, -, a2, b2⟩ := hp2
  have c1 : i.1 * Dd + i.2.1 < j.1 * Dd + j.2.2.1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt a1 b2)
  have c2 : j.1 * Dd + j.2.1 < i.1 * Dd + i.2.2.1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt a2 b1)
  have fi := row_facts hL i.2 hi
  have fj := row_facts hL j.2 hj
  have hBi := fi.2.1
  have hBj := fj.2.1
  rw [Dd_eq] at c1 c2 hBi hBj
  have hm : i.1 = j.1 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h <;> omega
  have ht : i.2 ≠ j.2 := fun h => hij (Prod.ext hm h)
  rw [hm] at c1 c2
  rcases pairwise_or L (rows_pairwise hL hc) i.2 hi j.2 hj ht with h | h <;> omega

/-! ## Chebyshev θ on the intervals -/

lemma theta_eq_filter (N c : ℕ) (hc : 0 < c) :
    Chebyshev.theta ((N : ℝ) / c) =
      ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ c * p ≤ N), Real.log p := by
  rw [Chebyshev.theta]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hc']
  constructor
  · rintro ⟨⟨_, hpN⟩, hpp⟩
    have h1 : ((c * p : ℕ) : ℝ) ≤ N := by push_cast; linarith
    have h2 : c * p ≤ N := by exact_mod_cast h1
    refine ⟨?_, hpp, h2⟩
    have : p ≤ c * p := Nat.le_mul_of_pos_left p hc
    omega
  · rintro ⟨_, hpp, hcp⟩
    refine ⟨⟨hpp.pos, ?_⟩, hpp⟩
    have : ((c * p : ℕ) : ℝ) ≤ N := by exact_mod_cast hcp
    push_cast at this
    linarith

lemma Iset_sum (n m : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ) (hA : 0 < t.1) (hAB : t.1 < t.2.1) :
    ∑ p ∈ Iset n m t, Real.log p =
      Chebyshev.theta (((n * Dd : ℕ) : ℝ) / ((m * Dd + t.1 : ℕ) : ℝ)) -
      Chebyshev.theta (((n * Dd : ℕ) : ℝ) / ((m * Dd + t.2.1 : ℕ) : ℝ)) := by
  rw [theta_eq_filter _ _ (by omega), theta_eq_filter _ _ (by omega)]
  have hsub : (range (n * Dd + 1)).filter (fun p => p.Prime ∧ (m * Dd + t.2.1) * p ≤ n * Dd) ⊆
      (range (n * Dd + 1)).filter (fun p => p.Prime ∧ (m * Dd + t.1) * p ≤ n * Dd) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    refine ⟨hp.1, hp.2.1, le_trans ?_ hp.2.2⟩
    apply Nat.mul_le_mul_right; omega
  have hI : Iset n m t = (range (n * Dd + 1)).filter (fun p => p.Prime ∧ (m * Dd + t.1) * p ≤ n * Dd) \
      (range (n * Dd + 1)).filter (fun p => p.Prime ∧ (m * Dd + t.2.1) * p ≤ n * Dd) := by
    ext p
    simp only [Iset, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2, h3⟩, fun h => absurd h.2.2 (not_le.2 h4)⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h2, h3, not_le.1 fun h => h4 ⟨h1, h2, h⟩⟩
  rw [hI, ← Finset.sum_sdiff hsub]
  ring

lemma theta_pair_eventually (hθ : ∀ ε > 0, ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ ε * x)
    (α β ε : ℝ) (hα : 0 < α) (hβ : 0 < β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (α - β - ε * (α + β)) * n ≤
      Chebyshev.theta (n * α) - Chebyshev.theta (n * β) := by
  have tα : Tendsto (fun n : ℕ => (n : ℝ) * α) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hα
  have tβ : Tendsto (fun n : ℕ => (n : ℝ) * β) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hβ
  filter_upwards [tα.eventually (hθ ε hε), tβ.eventually (hθ ε hε)] with n h1 h2
  rw [abs_le] at h1 h2
  nlinarith [h1.1, h2.2]

lemma sqrt_isLittleO : (fun x : ℝ => Real.sqrt x) =o[atTop] (fun x : ℝ => x) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [eventually_ge_atTop (1 / c ^ 2)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hsq : (1 / c) ^ 2 ≤ x := by rw [div_pow, one_pow]; exact hx
  have hs : 1 / c ≤ Real.sqrt x := by
    calc 1 / c = Real.sqrt ((1 / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hsq
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg x), Real.norm_of_nonneg hx0.le]
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have h1 : 1 ≤ c * Real.sqrt x := by
    rw [div_le_iff₀ hc] at hs; linarith
  nlinarith [Real.sqrt_nonneg x]

/-- `θ(x) = x + o(x)` from the MediumPNT statement (platform node 7cfa31c8). -/
lemma theta_of_MediumPNT
    (h : ∃ c > 0, (Chebyshev.psi - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    ∀ ε > 0, ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ ε * x := by
  obtain ⟨c, hc, hO⟩ := h
  have he : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply Tendsto.const_mul_atTop_of_neg (by linarith)
    exact (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have h1 : (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) =o[atTop]
      (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).2 he
  have h2 := (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO h1
  have hg : (fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) =o[atTop]
      (fun x : ℝ => x) := h2.congr_right (fun x => mul_one x)
  have hpsi : (Chebyshev.psi - id) =o[atTop] (fun x : ℝ => x) := hO.trans_isLittleO hg
  have hdiff : (Chebyshev.psi - Chebyshev.theta) =o[atTop] (fun x : ℝ => x) :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO sqrt_isLittleO
  have htheta : (fun x => Chebyshev.theta x - x) =o[atTop] (fun x : ℝ => x) := by
    refine (hpsi.sub hdiff).congr_left (fun x => ?_)
    simp only [Pi.sub_apply, id]
    ring
  intro ε hε
  filter_upwards [htheta.def hε, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0] at hx
  exact hx

/-! ## Assembly -/

lemma lam_eq_sum (hL : L.all okRow = true) (hc : chainOk L = true) (K : ℕ) :
    PiIrrationality.Bai.lam L K = ∑ i ∈ range K ×ˢ L.toFinset, term i.1 i.2 := by
  rw [PiIrrationality.Bai.lam, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m _
  rw [List.sum_toFinset _ (rows_nodup hL hc)]

/-- **Prime saving, `λ_K` form** (the analogue of moona3k's `ZZEven.phi_lower`, 89f94235): for every `K` and
`δ > 0`, `Φ_n ≥ exp((λ_K - δ) n)` for all large `n`, given `θ(x) = x + o(x)`. -/
theorem phi_lower_lam_of_theta (hL : L.all okRow = true) (hc : chainOk L = true)
    (hθ : ∀ ε > 0, ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ ε * x) (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((PiIrrationality.Bai.lam L K - δ) * (n : ℝ)) ≤ (PiIrrationality.Bai.Phi n : ℝ) := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ)), S = range K ×ˢ L.toFinset := ⟨_, rfl⟩
  set α : ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ) → ℝ := fun i => (Dd : ℝ) / ((i.1 : ℝ) * Dd + i.2.1) with hα
  set β : ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ) → ℝ := fun i => (Dd : ℝ) / ((i.1 : ℝ) * Dd + i.2.2.1) with hβ
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (S.card : ℝ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hcdef]; exact Nat.cast_nonneg _
  set ε : ℝ := δ / (2 * 7430 * (c + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hD : (0 : ℝ) < Dd := by rw [Dd_eq]; norm_num
  have hmemS : ∀ i ∈ S, i.1 < K ∧ i.2 ∈ L := by
    intro i hi
    rw [hS, Finset.mem_product, Finset.mem_range, List.mem_toFinset] at hi
    exact hi
  have hApos : ∀ i ∈ S, (0 : ℝ) < (i.1 : ℝ) * Dd + i.2.1 := by
    intro i hi
    have : (0 : ℝ) < i.2.1 := by exact_mod_cast row_A_pos hL i.2 (hmemS i hi).2
    positivity
  have hBpos : ∀ i ∈ S, (0 : ℝ) < (i.1 : ℝ) * Dd + i.2.2.1 := by
    intro i hi
    have : (0 : ℝ) < i.2.2.1 := by
      exact_mod_cast lt_trans (row_A_pos hL i.2 (hmemS i hi).2) (row_facts hL i.2 (hmemS i hi).2).1
    positivity
  have hαβ : ∀ i ∈ S, α i + β i ≤ 2 * 7430 := by
    intro i hi
    have hr := (hmemS i hi).2
    have hA : (0 : ℝ) < i.2.1 := by exact_mod_cast row_A_pos hL i.2 hr
    have h3 : (Dd : ℝ) ≤ 7430 * i.2.1 := by exact_mod_cast (row_facts hL i.2 hr).2.2.1
    have hAB : (i.2.1 : ℝ) ≤ i.2.2.1 := by exact_mod_cast (row_facts hL i.2 hr).1.le
    have hm0 : (0 : ℝ) ≤ (i.1 : ℝ) * Dd := by positivity
    have ha : α i ≤ 7430 := by
      simp only [hα]
      rw [div_le_iff₀ (hApos i hi)]; nlinarith
    have hb : β i ≤ 7430 := by
      simp only [hβ]
      rw [div_le_iff₀ (hBpos i hi)]; nlinarith
    linarith
  have hev : ∀ᶠ n : ℕ in atTop, ∀ i ∈ S, (α i - β i - ε * (α i + β i)) * n ≤
      Chebyshev.theta (n * α i) - Chebyshev.theta (n * β i) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact theta_pair_eventually hθ _ _ _ (div_pos hD (hApos i hi)) (div_pos hD (hBpos i hi)) hε
  filter_upwards [hev, eventually_ge_atTop (7430 * K ^ 2)] with n hn hnK
  -- log Φ_n
  have hPhi_pos : (0 : ℝ) < (PiIrrationality.Bai.Phi n : ℝ) := by
    have : 0 < PiIrrationality.Bai.Phi n := by
      unfold PiIrrationality.Bai.Phi
      apply Finset.prod_pos
      intro p hp
      simp only [PiIrrationality.Bai.deletedPrimes, Finset.mem_filter] at hp
      exact hp.2.1.pos
    exact_mod_cast this
  have hlog : Real.log (PiIrrationality.Bai.Phi n : ℝ) =
      ∑ p ∈ PiIrrationality.Bai.deletedPrimes n, Real.log p := by
    unfold PiIrrationality.Bai.Phi
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    simp only [PiIrrationality.Bai.deletedPrimes, Finset.mem_filter] at hp
    exact_mod_cast hp.2.1.ne_zero
  -- the union of the intervals
  have hdisj : (S : Set (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ))).PairwiseDisjoint (fun i => Iset n i.1 i.2) := by
    intro i hi j hj hij
    exact Iset_disjoint hL hc n i j (hmemS i hi).2 (hmemS j hj).2 hij
  have hsubset : S.biUnion (fun i => Iset n i.1 i.2) ⊆ PiIrrationality.Bai.deletedPrimes n := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    exact mem_deleted hL K n i.1 p i.2 (hmemS i hi).2 (hmemS i hi).1 hnK hpi
  have hge : ∑ i ∈ S, (Chebyshev.theta (n * α i) - Chebyshev.theta (n * β i)) ≤
      ∑ p ∈ PiIrrationality.Bai.deletedPrimes n, Real.log p := by
    calc ∑ i ∈ S, (Chebyshev.theta (n * α i) - Chebyshev.theta (n * β i))
        = ∑ i ∈ S, ∑ p ∈ Iset n i.1 i.2, Real.log p := by
          apply Finset.sum_congr rfl
          intro i hi
          have hr := (hmemS i hi).2
          rw [Iset_sum n i.1 i.2 (row_A_pos hL i.2 hr) (row_facts hL i.2 hr).1]
          simp only [hα, hβ]
          push_cast
          rw [mul_div_assoc, mul_div_assoc]
      _ = ∑ p ∈ S.biUnion (fun i => Iset n i.1 i.2), Real.log p := (Finset.sum_biUnion hdisj).symm
      _ ≤ ∑ p ∈ PiIrrationality.Bai.deletedPrimes n, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p _ _ => Real.log_natCast_nonneg p)
  -- the main-term sum
  have hlam : ∑ i ∈ S, (α i - β i) = PiIrrationality.Bai.lam L K := by
    rw [lam_eq_sum hL hc, hS]
    exact Finset.sum_congr rfl (fun i _ => rfl)
  have hlow : (PiIrrationality.Bai.lam L K - δ) * n ≤ ∑ i ∈ S, (Chebyshev.theta (n * α i) - Chebyshev.theta (n * β i)) := by
    have h1 : ∑ i ∈ S, (α i - β i - ε * (α i + β i)) * n ≤
        ∑ i ∈ S, (Chebyshev.theta (n * α i) - Chebyshev.theta (n * β i)) := Finset.sum_le_sum hn
    have h2 : ∑ i ∈ S, ε * (α i + β i) ≤ ∑ i ∈ S, ε * (2 * 7430) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hαβ i hi) hε.le
    have h3 : ∑ i ∈ S, ε * (2 * 7430) ≤ δ := by
      rw [Finset.sum_const, nsmul_eq_mul, ← hcdef, hεdef]
      have e : c * (δ / (2 * 7430 * (c + 1)) * (2 * 7430)) = δ * (c / (c + 1)) := by
        field_simp
      rw [e]
      have : c / (c + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      nlinarith
    have h4 : ∑ i ∈ S, (α i - β i - ε * (α i + β i)) * n =
        (∑ i ∈ S, (α i - β i) - ∑ i ∈ S, ε * (α i + β i)) * n := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    rw [h4, hlam] at h1
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc Real.exp ((PiIrrationality.Bai.lam L K - δ) * (n : ℝ))
      ≤ Real.exp (Real.log (PiIrrationality.Bai.Phi n : ℝ)) := by
        apply Real.exp_le_exp.2
        rw [hlog]
        linarith
    _ = (PiIrrationality.Bai.Phi n : ℝ) := Real.exp_log hPhi_pos

/-- **Prime saving for any admissible table** `L`, assuming the MediumPNT statement (platform node 7cfa31c8). -/
theorem phi_lower_lam_of_MediumPNT
    (L : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (hL : L.all PiIrrationality.Bai.okRow = true)
    (hc : PiIrrationality.Bai.chainOk L = true)
    (hPNT : ∃ c > 0, (Chebyshev.psi - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
    (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((PiIrrationality.Bai.lam L K - δ) * (n : ℝ)) ≤ (PiIrrationality.Bai.Phi n : ℝ) :=
  phi_lower_lam_of_theta hL hc (theta_of_MediumPNT hPNT) K δ hδ

end PiIrrationality.BaiPhi
end

open Filter in
theorem solution
    (L : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (hL : L.all PiIrrationality.Bai.okRow = true)
    (hc : PiIrrationality.Bai.chainOk L = true)
    (hPNT : ∃ c > 0, (Chebyshev.psi - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
    (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((PiIrrationality.Bai.lam L K - δ) * (n : ℝ)) ≤ (PiIrrationality.Bai.Phi n : ℝ) := by
  exact PiIrrationality.BaiPhi.phi_lower_lam_of_MediumPNT L hL hc hPNT K δ hδ

-- Prove2me | solution 2 for SLPEPricing.Regret.containment
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:48:12.854569+00:00
-- url     : https://prove2.me/submissions/45c47855-c650-49ae-8645-d2c465efe99b

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

open SLPEPricing.Regret

namespace L4CE

noncomputable def dd : ℝ → ℝ := fun x => (1 - x) / 200 + (x - 1 / 2) ^ 3 / 300
noncomputable def d1 : ℝ → ℝ := fun x => -1 / 200 + (x - 1 / 2) ^ 2 / 100
noncomputable def d2 : ℝ → ℝ := fun x => (x - 1 / 2) / 50

lemma hd0 (x : ℝ) : HasDerivAt dd (d1 x) x := by
  unfold dd d1
  have h1 := ((hasDerivAt_id' x).const_sub 1).div_const 200
  have h2 := (((hasDerivAt_id' x).sub_const (1 / 2)).pow 3).div_const 300
  refine (h1.add h2).congr_deriv ?_
  push_cast; ring

lemma hd1 (x : ℝ) : HasDerivAt d1 (d2 x) x := by
  unfold d1 d2
  have h2 := (((hasDerivAt_id' x).sub_const (1 / 2)).pow 2).div_const 100
  refine (h2.const_add (-1 / 200)).congr_deriv ?_
  push_cast; ring

lemma hd2 (x : ℝ) : HasDerivAt d2 (1 / 50) x := by
  unfold d2
  have h2 := ((hasDerivAt_id' x).sub_const (1 / 2)).div_const 50
  convert h2 using 1

lemma deriv_dd : deriv dd = d1 := funext fun x => (hd0 x).deriv
lemma deriv_d1 : deriv d1 = d2 := funext fun x => (hd1 x).deriv
lemma deriv_d2 : deriv d2 = fun _ => 1 / 50 := funext fun x => (hd2 x).deriv

lemma it1 : iteratedDeriv 1 dd = d1 := by rw [iteratedDeriv_one, deriv_dd]
lemma it2 : iteratedDeriv 2 dd = d2 := by rw [iteratedDeriv_succ, it1, deriv_d1]
lemma it3 : iteratedDeriv 3 dd = fun _ => 1 / 50 := by rw [iteratedDeriv_succ, it2, deriv_d2]

lemma standing : Standing dd (1 / 2) (1 / 200) (3 / 100) (7 / 800) (19 / 10) 10 where
  smooth := by unfold dd; fun_prop
  antitone := by
    intro x hx y hy hxy
    simp only [Set.mem_Icc] at hx hy
    unfold dd
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sq_nonneg (x - y)),
      mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hx.1 hy.1),
      mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)),
      mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hx.1 (sub_nonneg.mpr hy.2)),
      mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hy.1 (sub_nonneg.mpr hx.2))]
  nonneg := by
    intro p hp
    simp only [Set.mem_Icc] at hp
    unfold dd
    nlinarith [mul_nonneg (sq_nonneg (1 - p)) (by linarith : (0:ℝ) ≤ 3 - 2 * (1 - p)), hp.1, hp.2]
  pstar_pos := by norm_num
  pstar_lt_one := by norm_num
  unique_max := by
    intro p hp hne
    simp only [Set.mem_Icc] at hp
    simp only [r, dd]
    have hy : 0 < (p - 1 / 2) ^ 2 := by
      have : p - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
      positivity
    have hfac : 0 < 1 / 200 - (p - 1 / 2) / 600 - (p - 1 / 2) ^ 2 / 300 := by nlinarith
    have : (1 / 2 : ℝ) * ((1 - 1 / 2) / 200 + (1 / 2 - 1 / 2) ^ 3 / 300) -
        p * ((1 - p) / 200 + (p - 1 / 2) ^ 3 / 300) =
        (p - 1 / 2) ^ 2 * (1 / 200 - (p - 1 / 2) / 600 - (p - 1 / 2) ^ 2 / 300) := by ring
    nlinarith [mul_pos hy hfac]
  kappa_pos := by norm_num
  assumption1 := by
    intro p _
    rw [deriv_dd]; unfold dd d1
    nlinarith [sq_nonneg (p - 1 / 2)]
  K1_bound := by
    intro k hk p hp
    simp only [Set.mem_Icc] at hp
    interval_cases k
    · simp only [iteratedDeriv_zero]; unfold dd
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p - 1 / 2), sq_nonneg (p + 1 / 2),
        mul_nonneg (sub_nonneg.mpr hp.2) (by linarith [hp.1] : (0:ℝ) ≤ p + 1),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hp.2) (by linarith [hp.1] : (0:ℝ) ≤ p + 1))
          (by linarith [hp.1] : (0:ℝ) ≤ p + 1),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hp.2) (by linarith [hp.1] : (0:ℝ) ≤ p + 1))
          (sub_nonneg.mpr hp.2)]
    · rw [it1]; unfold d1
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p - 1 / 2),
        mul_nonneg (sub_nonneg.mpr hp.2) (by linarith [hp.1] : (0:ℝ) ≤ p + 1)]
    · rw [it2]; unfold d2
      rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
    · rw [it3]; norm_num
  c_pos := by norm_num
  gradient := by
    rw [deriv_dd]; unfold d1; norm_num [abs_of_neg]
  rho_pos := by norm_num
  mu_ge := by unfold Mconst; norm_num
  mu_lt := by norm_num


noncomputable def amaxC : (ℝ → ℝ) → ℝ → ℝ → ℝ := fun f a b =>
  Classical.epsilon (fun x => x ∈ Set.Icc a b ∧ ∀ y ∈ Set.Icc a b, f y ≤ f x)

lemma amaxC_sel : IsArgmaxSelector amaxC := by
  intro f a b hab hf
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hf
  exact Classical.epsilon_spec (p := fun x => x ∈ Set.Icc a b ∧ ∀ y ∈ Set.Icc a b, f y ≤ f x)
    ⟨x, hx, fun y hy => hmax hy⟩

lemma amaxC_eq (f : ℝ → ℝ) (a b x0 : ℝ) (hx0 : x0 ∈ Set.Icc a b)
    (huniq : ∀ y ∈ Set.Icc a b, y ≠ x0 → f y < f x0) : amaxC f a b = x0 := by
  have hex : ∃ x, x ∈ Set.Icc a b ∧ ∀ y ∈ Set.Icc a b, f y ≤ f x :=
    ⟨x0, hx0, fun y hy => by
      rcases eq_or_ne y x0 with h | h
      · rw [h]
      · exact (huniq y hy h).le⟩
  have hs := Classical.epsilon_spec hex
  by_contra hne
  have h1 := huniq _ hs.1 hne
  have h2 := hs.2 x0 hx0
  unfold amaxC at hne h1 h2
  linarith

noncomputable abbrev μ0 : ℝ := 19 / 10
noncomputable abbrev ρ0 : ℝ := 10

noncomputable def sel0 : ℕ → ℕ × ℕ × ℕ × ℕ := fun i =>
  (roundStart μ0 ρ0 2 i, roundStart μ0 ρ0 2 i + nRound μ0 ρ0 2 i,
    roundStart μ0 ρ0 2 i + nRound μ0 ρ0 2 i, roundStart μ0 ρ0 2 i + 2 * nRound μ0 ρ0 2 i)

noncomputable def ε0 : ℕ → ℝ := fun t => if t < roundStart μ0 ρ0 2 2 then 1 / 400 else 361 / 160000

lemma delta_pos (i : ℕ) : 0 < Delta μ0 i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, ih with
    | 0, _ => simp [Delta]
    | 1, _ => simp [Delta]
    | (k + 2), ih =>
      have : Delta μ0 (k + 2) = μ0 * Delta μ0 (k + 1) ^ 2 := rfl
      rw [this]; have := ih (k + 1) (by omega); positivity

lemma n_pos (i : ℕ) : 1 ≤ nRound μ0 ρ0 2 i := by
  unfold nRound
  rw [Nat.one_le_ceil_iff]
  have := Real.log_pos (by norm_num : (1 : ℝ) < (2 : ℕ))
  have := delta_pos i
  positivity

lemma rs1 : roundStart μ0 ρ0 2 1 = 0 := by simp [roundStart]
lemma rs2 : roundStart μ0 ρ0 2 2 = 3 * nRound μ0 ρ0 2 1 := by simp [roundStart]

/-- noise is constant `e` on the periods of a round -/
lemma avg_eq (i : ℕ) (q e : ℝ)
    (hε : ∀ t, roundStart μ0 ρ0 2 i ≤ t → t < roundStart μ0 ρ0 2 i + 3 * nRound μ0 ρ0 2 i →
      ε0 t = e) :
    (1 / (nRound μ0 ρ0 2 i : ℝ)) * ∑ t ∈ Finset.Ico (roundStart μ0 ρ0 2 i + nRound μ0 ρ0 2 i)
      (roundStart μ0 ρ0 2 i + 2 * nRound μ0 ρ0 2 i),
      (dd (blockPrice q (Delta μ0 i) (roundStart μ0 ρ0 2 i) (nRound μ0 ρ0 2 i) t) + ε0 t) =
    dd q + e := by
  have hn := n_pos i
  rw [Finset.sum_congr rfl (g := fun _ => dd q + e)]
  · rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : roundStart μ0 ρ0 2 i + 2 * nRound μ0 ρ0 2 i - (roundStart μ0 ρ0 2 i + nRound μ0 ρ0 2 i)
        = nRound μ0 ρ0 2 i := by omega
    rw [this]
    have : (nRound μ0 ρ0 2 i : ℝ) ≠ 0 := by exact_mod_cast (by omega : nRound μ0 ρ0 2 i ≠ 0)
    field_simp
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    unfold blockPrice
    rw [if_neg (by omega), if_pos ht.2, hε t (by omega) (by omega)]

lemma round_eq (i : ℕ) (q e : ℝ)
    (hε : ∀ t, roundStart μ0 ρ0 2 i ≤ t → t < roundStart μ0 ρ0 2 i + 3 * nRound μ0 ρ0 2 i →
      ε0 t = e) :
    roundUpdate (fun p t => dd p + ε0 t) μ0 ρ0 amaxC sel0 2 i q =
      amaxC (fun p => p * dest (Delta μ0 i) q (dd q + e) (dd (q - Delta μ0 i) + e) (dd q + e)
        (dd q + e) (dd (q + Delta μ0 i) + e) p) (q - Delta μ0 i) (q + Delta μ0 i) := by
  have hn := n_pos i
  have hav := avg_eq i q e hε
  set s := roundStart μ0 ρ0 2 i
  set n := nRound μ0 ρ0 2 i
  have b1 : blockPrice q (Delta μ0 i) s n s = q - Delta μ0 i := by
    unfold blockPrice; rw [if_pos (by omega)]
  have b2 : blockPrice q (Delta μ0 i) s n (s + n) = q := by
    unfold blockPrice; rw [if_neg (by omega), if_pos (by omega)]
  have b3 : blockPrice q (Delta μ0 i) s n (s + 2 * n) = q + Delta μ0 i := by
    unfold blockPrice; rw [if_neg (by omega), if_neg (by omega)]
  simp only [roundUpdate, estimate, sel0]
  rw [hav, b1, b2, b3, hε _ le_rfl (by omega), hε _ (by omega) (by omega),
    hε _ (by omega) (by omega)]

lemma eps1 (t : ℕ) (h1 : roundStart μ0 ρ0 2 1 ≤ t)
    (h2 : t < roundStart μ0 ρ0 2 1 + 3 * nRound μ0 ρ0 2 1) : ε0 t = 1 / 400 := by
  unfold ε0; rw [if_pos (by rw [rs2]; rw [rs1] at h2; omega)]

lemma eps2 (t : ℕ) (h1 : roundStart μ0 ρ0 2 2 ≤ t)
    (_h2 : t < roundStart μ0 ρ0 2 2 + 3 * nRound μ0 ρ0 2 2) : ε0 t = 361 / 160000 := by
  unfold ε0; rw [if_neg (by omega)]

lemma D1 : Delta μ0 1 = 1 / 2 := rfl
lemma D2 : Delta μ0 2 = 19 / 40 := by
  show (19 / 10 : ℝ) * (1 / 2) ^ 2 = 19 / 40; norm_num

lemma centre2 : policyCentre (fun p t => dd p + ε0 t) μ0 ρ0 amaxC sel0 2 2 = 17 / 20 := by
  show roundUpdate (fun p t => dd p + ε0 t) μ0 ρ0 amaxC sel0 2 1 (1 / 2) = 17 / 20
  rw [round_eq 1 (1 / 2) (1 / 400) eps1, D1]
  apply amaxC_eq
  · constructor <;> norm_num
  · intro y hy hne
    simp only [Set.mem_Icc] at hy
    have hy2 : 0 < (y - 17 / 20) ^ 2 := by
      have : y - 17 / 20 ≠ 0 := sub_ne_zero.mpr hne
      positivity
    unfold dest dd
    split_ifs <;> norm_num <;> nlinarith

lemma centre3 : policyCentre (fun p t => dd p + ε0 t) μ0 ρ0 amaxC sel0 2 3 = 53 / 40 := by
  show roundUpdate (fun p t => dd p + ε0 t) μ0 ρ0 amaxC sel0 2 2
    (policyCentre (fun p t => dd p + ε0 t) μ0 ρ0 amaxC sel0 2 2) = 53 / 40
  rw [centre2, round_eq 2 (17 / 20) (361 / 160000) eps2, D2]
  apply amaxC_eq
  · constructor <;> norm_num
  · intro y hy hne
    simp only [Set.mem_Icc] at hy
    have hlt : y < 53 / 40 := lt_of_le_of_ne (by linarith [hy.2]) hne
    unfold dest dd
    rw [if_neg (show ¬ ((53 : ℝ) / 40 ≤ 17 / 20) by norm_num)]
    split_ifs with hyq
    · norm_num
      nlinarith [sq_nonneg (y - 13693 / 17992)]
    · norm_num
      nlinarith

end L4CE

open L4CE

theorem solution : ¬ (∀ (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ), Standing d pstar κ K₁ c μ ρ →
    ∀ (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ), IsArgmaxSelector amax →
    ∀ (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ), 2 ≤ T → ∀ (i : ℕ), 1 ≤ i →
    (∀ j ∈ Finset.Ico 1 i,
      Assumption2At μ ρ T sel ε j ∧ ConcentrationAt d μ ρ amax sel ε T j) →
    pL d μ ρ amax sel ε T i ≤ pstar ∧ pstar ≤ pH d μ ρ amax sel ε T i) := by
  intro H
  have hgood : ∀ j ∈ Finset.Ico 1 3,
      Assumption2At μ0 ρ0 2 sel0 ε0 j ∧ ConcentrationAt dd μ0 ρ0 amaxC sel0 ε0 2 j := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hn := n_pos j
    obtain ⟨e, he, hebd⟩ : ∃ e : ℝ, (∀ t, roundStart μ0 ρ0 2 j ≤ t →
        t < roundStart μ0 ρ0 2 j + 3 * nRound μ0 ρ0 2 j → ε0 t = e) ∧
        |e| ≤ Delta μ0 j ^ 2 / ρ0 ^ 2 := by
      rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
      · exact ⟨1 / 400, eps1, by rw [D1]; norm_num⟩
      · exact ⟨361 / 160000, eps2, by rw [D2]; norm_num⟩
    constructor
    · unfold Assumption2At sel0
      simp only
      refine ⟨⟨le_rfl, by omega⟩, ⟨le_rfl, by omega⟩, ⟨le_rfl, by omega⟩, ⟨le_rfl, by omega⟩, ?_, ?_⟩
      · rw [he _ le_rfl (by omega), he _ (by omega) (by omega)]
      · rw [he _ (by omega) (by omega), he _ (by omega) (by omega)]
    · unfold ConcentrationAt avgM roundObs
      rw [avg_eq j _ e he]
      unfold pM
      simpa using hebd
  have := H dd (1 / 2) (1 / 200) (3 / 100) (7 / 800) μ0 ρ0 standing amaxC amaxC_sel sel0 ε0 2
    le_rfl 3 (by norm_num) hgood
  have hc : centre dd μ0 ρ0 amaxC sel0 ε0 2 3 = 53 / 40 := centre3
  have hD3 : Delta μ0 3 = 6859 / 16000 := by
    show μ0 * Delta μ0 2 ^ 2 = 6859 / 16000
    rw [D2]; norm_num
  unfold pL at this
  rw [hc, hD3] at this
  norm_num at this

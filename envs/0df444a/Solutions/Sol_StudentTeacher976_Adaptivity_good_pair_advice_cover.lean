-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.good_pair_advice_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:46:15.431979+00:00
-- url     : https://prove2.me/submissions/8266ec1a-4202-4e54-8e56-ef55a1bde7b1

import Theorems.Thm_StudentTeacher976_Adaptivity_good_pair_exists
set_option autoImplicit false
open scoped BigOperators Classical

namespace StudentTeacher976.Adaptivity

/-- The counting step on p.20, before the iterative advice cover. -/
theorem dense_good_subset {α : Type*} [DecidableEq α] (U : Finset α)
    (k : ℕ) (hk : 0 < k) (hku : k ≤ U.card)
    (G : Finset α → α → Prop)
    (hgood : ∀ V ⊆ U, V.card = k → ∃ x ∈ V, G (V.erase x) x) :
    ∃ S ⊆ U, S.card = k - 1 ∧
      U.card - k + 1 ≤ k * (U.filter fun x => x ∉ S ∧ G S x).card := by
  classical
  let A := U.powersetCard (k - 1)
  let C := fun S : Finset α => U.filter fun x => x ∉ S ∧ G S x
  have hA : A.Nonempty := Finset.powersetCard_nonempty.mpr (by omega)
  obtain ⟨S, hS, hmax⟩ := A.exists_max_image (fun S => (C S).card) hA
  have hScard : S.card = k - 1 := (Finset.mem_powersetCard.mp hS).2
  have hSsub : S ⊆ U := (Finset.mem_powersetCard.mp hS).1
  let P := A.sigma C
  have hsurj : Set.SurjOn (fun p : (T : Finset α) × α => insert p.2 p.1)
      (P : Set ((T : Finset α) × α)) (U.powersetCard k : Set (Finset α)) := by
    intro V hV
    obtain ⟨hVU, hVk⟩ := Finset.mem_powersetCard.mp hV
    obtain ⟨x, hx, hG⟩ := hgood V hVU hVk
    refine ⟨⟨V.erase x, x⟩, ?_, Finset.insert_erase hx⟩
    simp only [P, Finset.mem_coe, Finset.mem_sigma, A, C, Finset.mem_powersetCard,
      Finset.mem_filter]
    exact ⟨⟨(Finset.erase_subset x V).trans hVU, by simp [Finset.card_erase_of_mem hx, hVk]⟩,
      hVU hx, Finset.notMem_erase x V, hG⟩
  have hcount : U.card.choose k ≤ A.card * (C S).card := by
    calc
      U.card.choose k = (U.powersetCard k).card := (Finset.card_powersetCard _ _).symm
      _ ≤ P.card := Finset.card_le_card_of_surjOn _ hsurj
      _ = ∑ T ∈ A, (C T).card := Finset.card_sigma _ _
      _ ≤ ∑ _T ∈ A, (C S).card := Finset.sum_le_sum fun T hT => hmax T hT
      _ = A.card * (C S).card := by simp
  have hidentity : U.card.choose k * k = U.card.choose (k - 1) * (U.card - k + 1) := by
    have hchoose := Nat.choose_succ_right_eq U.card (k - 1)
    rw [show U.card - (k - 1) = U.card - k + 1 by omega] at hchoose
    simpa [Nat.sub_add_cancel hk] using hchoose
  have hApos : 0 < U.card.choose (k - 1) := Nat.choose_pos (by omega)
  refine ⟨S, hSsub, hScard, ?_⟩
  have hm := Nat.mul_le_mul_right k hcount
  rw [hidentity] at hm
  have hcardA : A.card = U.card.choose (k - 1) := Finset.card_powersetCard _ _
  rw [hcardA] at hm
  nlinarith

private theorem contraction_step {α : Type*} [DecidableEq α] (U : Finset α)
    (k : ℕ) (hk : 0 < k) (hku : k ≤ U.card) (G : Finset α → α → Prop)
    (hgood : ∀ V ⊆ U, V.card = k → ∃ x ∈ V, G (V.erase x) x) :
    ∃ S D : Finset α, S ⊆ U ∧ S.card = k - 1 ∧ D ⊆ U ∧
      (∀ x ∈ D, x ∈ S ∨ G S x) ∧
      k * (U \ D).card ≤ (k - 1) * U.card := by
  classical
  obtain ⟨S, hSU, hS, hden⟩ := dense_good_subset U k hk hku G hgood
  let C := U.filter fun x => x ∉ S ∧ G S x
  let D := S ∪ C
  have hDU : D ⊆ U := Finset.union_subset hSU (Finset.filter_subset _ _)
  have hdis : Disjoint S C := by
    rw [Finset.disjoint_left]
    intro x hx hxC
    exact (Finset.mem_filter.mp hxC).2.1 hx
  have hDcard : D.card = (k - 1) + C.card := by
    rw [Finset.card_union_of_disjoint hdis, hS]
  have hsum := Finset.card_sdiff_add_card_eq_card hDU
  refine ⟨S, D, hSU, hS, hDU, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mp h).2.2
  · dsimp [C] at hDcard
    have hkadd : k - 1 + 1 = k := by omega
    have hN : U.card - k + 1 + (k - 1) = U.card := by omega
    nlinarith [Nat.zero_le ((k - 1) * (k - 1))]

private theorem ratio_pow_le_half (k : ℕ) (hk : 0 < k) :
    (((k : ℝ) - 1) / k) ^ k ≤ (1 / 2 : ℝ) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hk1 : k = 1
  · simp [hk1]
  have hkbig : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  let a : ℝ := 1 / ((k : ℝ) - 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ a by linarith) k
  have hbig : (2 : ℝ) ≤ (1 + a) ^ k := by
    have hka : (1 : ℝ) ≤ (k : ℝ) * a := by
      dsimp [a]
      rw [← mul_div_assoc, mul_one]
      exact (le_div_iff₀ (by linarith)).mpr (by linarith)
    linarith
  have hmul : (((k : ℝ) - 1) / k) * (1 + a) = 1 := by
    dsimp [a]
    field_simp [ne_of_gt hkreal, sub_ne_zero.mpr (ne_of_gt hkbig)]
    <;> ring
  have hp := congrArg (fun x : ℝ => x ^ k) hmul
  rw [mul_pow, one_pow] at hp
  have hnon : 0 ≤ (((k : ℝ) - 1) / k) ^ k := by positivity
  nlinarith

 theorem polynomial_good_pair_cover {α : Type*} [DecidableEq α]
    (U : Finset α) (n k : ℕ) (hk : 0 < k) (hU : U.card ≤ 2 ^ n)
    (G : Finset α → α → Prop)
    (hgood : ∀ V ⊆ U, V.card = k → ∃ x ∈ V, G (V.erase x) x) :
    ∃ A : List (Finset α), ∃ R : Finset α,
      A.length ≤ k * (n + 1) ∧
      (∀ S ∈ A, S ⊆ U ∧ S.card = k - 1) ∧ R ⊆ U ∧ R.card < k ∧
      ∀ x ∈ U, x ∈ R ∨ ∃ S ∈ A, x ∈ S ∨ G S x := by
  classical
  let rho : ℝ := ((k : ℝ) - 1) / k
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hrho : 0 ≤ rho := by
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_nonneg (by linarith) hkreal.le
  have hind : ∀ t : ℕ, ∃ A : List (Finset α), ∃ R : Finset α,
      A.length ≤ t ∧ (∀ S ∈ A, S ⊆ U ∧ S.card = k - 1) ∧ R ⊆ U ∧
      (∀ x ∈ U, x ∈ R ∨ ∃ S ∈ A, x ∈ S ∨ G S x) ∧
      (R.card < k ∨ (R.card : ℝ) ≤ rho ^ t * U.card) := by
    intro t
    induction t with
    | zero => exact ⟨[], U, by simp, by simp, Finset.Subset.refl _,
        fun x hx => Or.inl hx, Or.inr (by simp)⟩
    | succ t ih =>
      obtain ⟨A, R, hA, hAS, hRU, hcover, hsize⟩ := ih
      by_cases hsmall : R.card < k
      · exact ⟨A, R, by omega, hAS, hRU, hcover, Or.inl hsmall⟩
      have hbound : (R.card : ℝ) ≤ rho ^ t * U.card := hsize.resolve_left hsmall
      obtain ⟨S, D, hSR, hS, hDR, hD, hcontract⟩ :=
        contraction_step R k hk (by omega) G (fun V hVR => hgood V (hVR.trans hRU))
      refine ⟨S :: A, R \ D, by simpa using (show A.length + 1 ≤ t + 1 by omega), ?_,
        (Finset.sdiff_subset).trans hRU, ?_, Or.inr ?_⟩
      · intro T hT
        rcases List.mem_cons.mp hT with rfl | hT
        · exact ⟨hSR.trans hRU, hS⟩
        · exact hAS T hT
      · intro x hx
        rcases hcover x hx with h | h
        · by_cases hxD : x ∈ D
          · exact Or.inr ⟨S, List.mem_cons_self, hD x hxD⟩
          · exact Or.inl (Finset.mem_sdiff.mpr ⟨h, hxD⟩)
        · obtain ⟨T, hT, hxT⟩ := h
          exact Or.inr ⟨T, List.mem_cons_of_mem _ hT, hxT⟩
      · have hc : (k : ℝ) * (R \ D).card ≤ ((k : ℝ) - 1) * R.card := by
          have hc' : k * (R \ D).card ≤ (k - 1) * R.card := hcontract
          have hcast : (k : ℝ) * (R \ D).card ≤ ((k - 1 : ℕ) : ℝ) * R.card := by exact_mod_cast hc'
          simpa [Nat.cast_sub (show 1 ≤ k by omega)] using hcast
        have hrnew : ((R \ D).card : ℝ) ≤ rho * R.card := by
          dsimp [rho]
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ hkreal).mpr
          nlinarith
        calc
          ((R \ D).card : ℝ) ≤ rho * R.card := hrnew
          _ ≤ rho * (rho ^ t * U.card) := mul_le_mul_of_nonneg_left hbound hrho
          _ = rho ^ (t + 1) * U.card := by rw [pow_succ]; ring
  obtain ⟨A, R, hA, hAS, hRU, hcover, hsize⟩ := hind (k * (n + 1))
  refine ⟨A, R, hA, hAS, hRU, ?_, hcover⟩
  rcases hsize with hsmall | hbound
  · exact hsmall
  · have hbase : rho ^ k ≤ (1 / 2 : ℝ) := ratio_pow_le_half k hk
    have hpow : rho ^ (k * (n + 1)) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg hrho _) hbase _
    have hUreal : (U.card : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hU
    have hhalf : (R.card : ℝ) ≤ 1 / 2 := by
      calc
        (R.card : ℝ) ≤ rho ^ (k * (n + 1)) * U.card := hbound
        _ ≤ (1 / 2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n :=
          mul_le_mul hpow hUreal (by positivity) (by positivity)
        _ = 1 / 2 := by rw [pow_succ, div_pow]; field_simp; ring
    have hlt : (R.card : ℝ) < 1 := by linarith
    have : R.card < 1 := by exact_mod_cast hlt
    omega

end StudentTeacher976.Adaptivity

open StudentTeacher976.Adaptivity

private theorem words_length (n : ℕ) : (wordsOfLength n).length = 2 ^ n := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih => simp [wordsOfLength, ih, pow_succ]; omega

private theorem words_mem (n : ℕ) (w : Word) : w ∈ wordsOfLength n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [wordsOfLength, List.length_eq_zero_iff]
  | succ n ih =>
    cases w with
    | nil => simp [wordsOfLength]
    | cons b w => cases b <;> simp [wordsOfLength, ih]

theorem solution (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (n k : ℕ) (hsize : k = resource r (n * k))
    (f : TupleStudent) (hf : UniformTupleStudent i f)
    (hshape : TupleStudentShape W n k (resource q (n * k)) f)
    (hsolve : TupleStudentWins W n k (resource q (n * k)) (normalize W f))
    (U : Finset Word) (hU : ∀ x, x ∈ U ↔ x ∈ positiveInputs W n) :
    ∃ A : List (Finset Word), ∃ R : Finset Word,
      A.length ≤ k * (n + 1) ∧
      (∀ S ∈ A, S ⊆ U ∧ S.card = k - 1) ∧ R ⊆ U ∧ R.card < k ∧
      ∀ x ∈ U, x ∈ R ∨ ∃ S ∈ A, x ∈ S ∨
        GoodPair W n k (resource q (n * k)) f S x := by
  classical
  have hk : 0 < k := by
    obtain ⟨ε, hε, hb⟩ := hr.2.2.2
    have hp := (hb (max 1 (n * k)) (by omega)).1
    rw [hsize]
    exact lt_of_lt_of_le Nat.zero_lt_one hp
  have hcard : U.card ≤ 2 ^ n := by
    calc
      U.card ≤ (wordsOfLength n).toFinset.card := Finset.card_le_card (by
        intro x hx
        exact List.mem_toFinset.mpr ((words_mem n x).mpr ((hU x).mp hx).1))
      _ ≤ (wordsOfLength n).length := List.toFinset_card_le _
      _ = 2 ^ n := words_length n
  apply polynomial_good_pair_cover U n k hk hcard
  intro V hVU hVk
  exact good_pair_exists i L W r q hr hq n k hsize f hf hshape hsolve V
    (fun x hx => (hU x).mp (hVU hx)) hVk

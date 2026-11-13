-- Prove2me | solution 1 for TernarySync.Alphabet.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:20:57.722001+00:00
-- url     : https://prove2.me/submissions/01336a54-74b3-42d8-91c9-9404c4b99647

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource

section
set_option autoImplicit false

namespace TernarySync.Dev.L42
open TernarySync.Alphabet

theorem codeword_length : ∀ (a : Fin 3) (r : Fin 2), (codeword a r).length = 18 := by decide

theorem codeword_inj : ∀ (a : Fin 3) (r r' : Fin 2), codeword a r = codeword a r' → r = r' := by
  decide

theorem W_cons (a : Fin 3) (T : List (Fin 3)) (R : Fin (a :: T).length → Fin 2) :
    W (a :: T) R = codeword a (R 0) ++ W T (fun i => R i.succ) := by
  simp [W, List.ofFn_succ]

theorem W_length : ∀ (T : List (Fin 3)) (R : Fin T.length → Fin 2), (W T R).length = 18 * T.length
  | [], R => by simp [W]
  | a :: T, R => by
    rw [W_cons, List.length_append, codeword_length, W_length T]
    simp; ring

theorem getW : ∀ (T : List (Fin 3)) (R : Fin T.length → Fin 2) (i : Fin T.length) (j : ℕ),
    j < 18 → (W T R)[18 * i.val + j]? = (codeword (T.get i) (R i))[j]?
  | [], R, i, j, hj => i.elim0
  | a :: T, R, i, j, hj => by
    rw [W_cons]
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add]
      rw [List.getElem?_append_left (by rw [codeword_length]; exact hj)]
      rfl
    | succ i' =>
      have h18 : (codeword a (R 0)).length = 18 := codeword_length _ _
      rw [List.getElem?_append_right (by rw [h18]; simp; omega)]
      rw [h18]
      have := getW T (fun i => R i.succ) i' j hj
      rw [show 18 * (i'.succ).val + j - 18 = 18 * i'.val + j by simp [Fin.val_succ]; omega]
      exact this

theorem fac_getElem? {α : Type*} (S : List α) (a b k : ℕ) :
    (factor S a b)[k]? = if k < b - a then S[a + k]? else none := by
  simp [factor, List.getElem?_take, List.getElem?_drop]

theorem factor_congr (T : List (Fin 3)) (R R' : Fin T.length → Fin 2) (a b : ℕ)
    (h : ∀ i : Fin T.length, a < 18 * i.val + 18 → 18 * i.val < b → R i = R' i) :
    factor (W T R) a b = factor (W T R') a b := by
  apply List.ext_getElem?
  intro k
  rw [fac_getElem?, fac_getElem?]
  by_cases hk : k < b - a
  · simp only [hk, if_true]
    by_cases hp : a + k < 18 * T.length
    · have hlt : (a + k) / 18 < T.length := by omega
      have e : a + k = 18 * ((⟨(a + k) / 18, hlt⟩ : Fin T.length).val) + (a + k) % 18 := by
        simp; omega
      rw [e, getW T R _ _ (by omega), getW T R' _ _ (by omega),
        h ⟨(a + k) / 18, hlt⟩ (by simp; omega) (by simp; omega)]
    · rw [List.getElem?_eq_none (by rw [W_length]; omega),
        List.getElem?_eq_none (by rw [W_length]; omega)]
  · simp [hk]

theorem blockX_block (T : List (Fin 3)) (R : Fin T.length → Fin 2) (t ℓ : ℕ) (i : Fin T.length)
    (h1 : t ≤ 18 * i.val) (h2 : 18 * i.val + 18 ≤ t + ℓ) (j : ℕ) (hj : j < 18) :
    (blockX T R t ℓ)[18 * i.val - t + j]? = (codeword (T.get i) (R i))[j]? := by
  unfold blockX
  rw [fac_getElem?, if_pos (by omega), show t + (18 * i.val - t + j) = 18 * i.val + j by omega]
  exact getW T R i j hj

theorem card_complete (N t ℓ : ℕ) (h : t + 2 * ℓ ≤ 18 * N) :
    (completeBlocks N t ℓ).card = (t + ℓ) / 18 - (t + 17) / 18 := by
  have : (completeBlocks N t ℓ).map Fin.valEmbedding = Finset.Ico ((t + 17) / 18) ((t + ℓ) / 18) := by
    ext n
    simp only [Finset.mem_map, completeBlocks, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      omega
    · intro hn
      exact ⟨⟨n, by omega⟩, ⟨by simp; omega, by simp; omega⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]

theorem unifProb_le_one {N : ℕ} (S : Set (Fin N → Fin 2)) (h : ∀ R ∈ S, ∀ R' ∈ S, R = R') :
    unifProb S ≤ 1 / (2 : ℝ) ^ N := by
  classical
  unfold unifProb
  have : (Finset.univ.filter fun R => R ∈ S).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact h a (Finset.mem_filter.mp ha).2 b (Finset.mem_filter.mp hb).2
  gcongr
  exact_mod_cast this

theorem unifProb_agree {N : ℕ} (I : Finset (Fin N)) (f : Fin N → Fin 2) :
    unifProb (agreeOff I f) = (2 : ℝ) ^ I.card / (2 : ℝ) ^ N := by
  classical
  unfold unifProb
  have : (Finset.univ.filter fun R => R ∈ agreeOff I f) =
      Fintype.piFinset (fun i => if i ∈ I then (Finset.univ : Finset (Fin 2)) else {f i}) := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, agreeOff, Set.mem_setOf_eq,
      Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i ∈ I
      · simp [hi]
      · simp [hi, h i hi]
    · intro h i hi
      have := h i
      simpa [hi] using this
  rw [this, Fintype.card_piFinset]
  congr 2
  have e : ∀ i : Fin N, (((if i ∈ I then (Finset.univ : Finset (Fin 2)) else {f i}).card : ℕ) : ℝ) =
      if i ∈ I then (2 : ℝ) else 1 := by
    intro i
    by_cases hi : i ∈ I <;> simp [hi]
  rw [Nat.cast_prod, Finset.prod_congr rfl (fun i _ => e i), Finset.prod_ite]
  simp

end TernarySync.Dev.L42

namespace TernarySync.Alphabet
open TernarySync.Dev.L42 in
theorem chk_lemma_4_2 (T : List (Fin 3)) (hT : IsSquareFree T) (t ℓ : ℕ) (hℓ : 1000 < ℓ)
    (ht : t + 2 * ℓ ≤ 18 * T.length) :
    (ℓ : ℝ) / 18 - 2 ≤ ((completeBlocks T.length t ℓ).card : ℝ) ∧
      ∀ f : Fin T.length → Fin 2,
        (∀ R ∈ agreeOff (completeBlocks T.length t ℓ) f, blockY T R t ℓ = blockY T f t ℓ) ∧
        ∀ x : List (Fin 3), x.length = ℓ →
          condProb {R | blockX T R t ℓ = x} (agreeOff (completeBlocks T.length t ℓ) f) ≤
              (2 : ℝ) ^ (-((completeBlocks T.length t ℓ).card : ℝ)) ∧
            (2 : ℝ) ^ (-((completeBlocks T.length t ℓ).card : ℝ)) ≤
              4 * Real.exp (-(Real.log 2 / 18) * (ℓ : ℝ)) := by
  set I := completeBlocks T.length t ℓ with hI
  have hcard : (ℓ : ℝ) / 18 - 2 ≤ (I.card : ℝ) := by
    have h := card_complete T.length t ℓ ht
    have h2 : ℓ ≤ 18 * I.card + 36 := by rw [hI, h]; omega
    have h3 : (ℓ : ℝ) ≤ 18 * (I.card : ℝ) + 36 := by exact_mod_cast h2
    linarith
  refine ⟨hcard, fun f => ⟨?_, fun x hx => ⟨?_, ?_⟩⟩⟩
  · intro R hR
    unfold blockY
    apply factor_congr
    intro i hi1 hi2
    apply hR
    simp only [hI, completeBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · have hB := unifProb_agree I f
    have hs : ∀ R ∈ {R | blockX T R t ℓ = x} ∩ agreeOff I f,
        ∀ R' ∈ {R | blockX T R t ℓ = x} ∩ agreeOff I f, R = R' := by
      rintro R ⟨hR1, hR2⟩ R' ⟨hR1', hR2'⟩
      funext i
      by_cases hi : i ∈ I
      · simp only [hI, completeBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have hRR : codeword (T.get i) (R i) = codeword (T.get i) (R' i) := by
          apply List.ext_getElem?
          intro j
          by_cases hj : j < 18
          · rw [← blockX_block T R t ℓ i hi.1 hi.2 j hj, ← blockX_block T R' t ℓ i hi.1 hi.2 j hj]
            simp only [Set.mem_setOf_eq] at hR1 hR1'
            rw [hR1, hR1']
          · rw [List.getElem?_eq_none (by rw [codeword_length]; omega),
              List.getElem?_eq_none (by rw [codeword_length]; omega)]
        exact codeword_inj _ _ _ hRR
      · have h1 := hR2 i (by simpa [hI] using hi)
        have h2 := hR2' i (by simpa [hI] using hi)
        rw [h1, h2]
    have hle := unifProb_le_one _ hs
    unfold condProb
    rw [hB]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ I.card / (2 : ℝ) ^ T.length := by positivity
    have hneg : (2 : ℝ) ^ (-((I.card : ℕ) : ℝ)) = 1 / (2 : ℝ) ^ I.card := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; simp
    rw [hneg]
    calc _ ≤ (1 / (2 : ℝ) ^ T.length) / ((2 : ℝ) ^ I.card / (2 : ℝ) ^ T.length) :=
          div_le_div_of_nonneg_right hle hpos.le
      _ = _ := by field_simp
  · rw [Real.rpow_def_of_pos (by norm_num)]
    have h4 : (4 : ℝ) = Real.exp (Real.log 2 * 2) := by
      rw [show Real.log 2 * 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add,
        Real.exp_log (by norm_num)]; norm_num
    rw [h4, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_lemma_4_2 := @TernarySync.Alphabet.chk_lemma_4_2

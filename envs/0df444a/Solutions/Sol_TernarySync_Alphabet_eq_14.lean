-- Prove2me | solution 1 for TernarySync.Alphabet.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:28:53.985049+00:00
-- url     : https://prove2.me/submissions/d8ad079f-aade-4301-94c2-93b6c3c51914

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource
import Theorems.Thm_TernarySync_Alphabet_lemma_4_2
import Theorems.Thm_TernarySync_Alphabet_eq_12

section
set_option autoImplicit false

namespace TernarySync.Dev.Eq14
open TernarySync.Alphabet

open Classical in
noncomputable def cnt {N : ℕ} (A : Set (Fin N → Fin 2)) : ℕ :=
  (Finset.univ.filter fun R => R ∈ A).card

theorem unifProb_eq {N : ℕ} (A : Set (Fin N → Fin 2)) : unifProb A = (cnt A : ℝ) / 2 ^ N := rfl

theorem codeword_length (a : Fin 3) (r : Fin 2) : (codeword a r).length = 18 := by
  fin_cases a <;> fin_cases r <;> rfl

theorem W_length (T : List (Fin 3)) (R : Fin T.length → Fin 2) : (W T R).length = 18 * T.length := by
  simp [W, List.length_flatten, List.map_ofFn, Function.comp_def, codeword_length]
  ring

theorem blockX_length (T : List (Fin 3)) (R : Fin T.length → Fin 2) (t ℓ : ℕ)
    (ht : t + 2 * ℓ ≤ 18 * T.length) : (blockX T R t ℓ).length = ℓ := by
  simp only [blockX, factor, List.length_take, List.length_drop, W_length]
  omega

theorem agreeOff_card_le {N : ℕ} (I : Finset (Fin N)) (f : Fin N → Fin 2) :
    cnt (agreeOff I f) ≤ 2 ^ I.card := by
  classical
  unfold cnt
  have h : (Finset.univ.filter fun R => R ∈ agreeOff I f).card ≤
      (Finset.univ : Finset (I → Fin 2)).card := by
    apply Finset.card_le_card_of_injOn (fun R (i : I) => R i.1)
    · intro R _; simp
    · intro R hR R' hR' h
      have hR : R ∈ agreeOff I f := by simpa using hR
      have hR' : R' ∈ agreeOff I f := by simpa using hR'
      replace hR : ∀ i, i ∉ I → R i = f i := hR
      replace hR' : ∀ i, i ∉ I → R' i = f i := hR'
      funext i
      by_cases hi : i ∈ I
      · exact congrFun h ⟨i, hi⟩
      · rw [hR i hi, hR' i hi]
  simpa using h

theorem class_le_one {N : ℕ} (I : Finset (Fin N)) (f : Fin N → Fin 2) (A : Set (Fin N → Fin 2))
    (hf : f ∈ agreeOff I f)
    (h : condProb A (agreeOff I f) ≤ (2 : ℝ) ^ (-(I.card : ℝ))) :
    cnt (A ∩ agreeOff I f) ≤ 1 := by
  classical
  have hpos : 0 < cnt (agreeOff I f) :=
    Finset.card_pos.2 ⟨f, by simpa using hf⟩
  have h2 : (0:ℝ) < unifProb (agreeOff I f) := by
    rw [unifProb_eq]; exact div_pos (by exact_mod_cast hpos) (by positivity)
  unfold condProb at h
  rw [div_le_iff₀ h2] at h
  simp only [unifProb_eq] at h
  have hc := agreeOff_card_le I f
  have e : (2:ℝ) ^ (-(I.card : ℝ)) = ((2:ℝ) ^ I.card)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [e] at h
  have h2N : (0:ℝ) < 2 ^ N := by positivity
  have h2s : (0:ℝ) < 2 ^ I.card := by positivity
  rw [div_le_iff₀ h2N] at h
  have : (cnt (A ∩ agreeOff I f) : ℝ) ≤ 1 := by
    have hc' : (cnt (agreeOff I f) : ℝ) ≤ 2 ^ I.card := by
      exact_mod_cast hc
    have h3 := h
    rw [mul_assoc, div_mul_cancel₀ _ h2N.ne'] at h3
    have h4 : ((2:ℝ) ^ I.card)⁻¹ * (cnt (agreeOff I f) : ℝ)
        ≤ ((2:ℝ) ^ I.card)⁻¹ * 2 ^ I.card := by gcongr
    rw [inv_mul_cancel₀ h2s.ne'] at h4
    linarith
  exact_mod_cast this


theorem delBall_finite (η : ℝ) (ℓ : ℕ) (y : List (Fin 3)) : (delBall η ℓ y).Finite :=
  (List.finite_length_eq (Fin 3) ℓ).subset (fun _ hx => hx.1)

theorem G_card {N : ℕ} (I : Finset (Fin N)) :
    (Fintype.piFinset (fun i : Fin N => if i ∈ I then ({0} : Finset (Fin 2)) else Finset.univ)).card
      = 2 ^ (N - I.card) := by
  rw [Fintype.card_piFinset]
  have : ∀ i : Fin N, (if i ∈ I then ({0} : Finset (Fin 2)) else Finset.univ).card
      = if i ∈ I then 1 else 2 := by
    intro i; split_ifs <;> simp
  simp_rw [this]
  rw [Finset.prod_ite]
  simp [Finset.filter_not, Finset.card_sdiff_of_subset]

theorem count_bound (T : List (Fin 3)) (t ℓ n : ℕ) (ht : t + 2 * ℓ ≤ 18 * T.length)
    (hB : ∀ y : List (Fin 3), y.length = ℓ → (delBall ((1:ℝ)/1000) ℓ y).ncard ≤ n)
    (hY : ∀ f : Fin T.length → Fin 2, ∀ R ∈ agreeOff (completeBlocks T.length t ℓ) f,
        blockY T R t ℓ = blockY T f t ℓ)
    (hX : ∀ f : Fin T.length → Fin 2, ∀ x : List (Fin 3), x.length = ℓ →
        condProb {R | blockX T R t ℓ = x} (agreeOff (completeBlocks T.length t ℓ) f) ≤
          (2 : ℝ) ^ (-((completeBlocks T.length t ℓ).card : ℝ))) :
    cnt (badEvent T t ℓ) ≤ n * 2 ^ (T.length - (completeBlocks T.length t ℓ).card) := by
  classical
  set I := completeBlocks T.length t ℓ with hI
  set g : (Fin T.length → Fin 2) → (Fin T.length → Fin 2) :=
    fun R i => if i ∈ I then 0 else R i with hg
  set Ef := Finset.univ.filter fun R => R ∈ badEvent T t ℓ with hEf
  have hcnt : cnt (badEvent T t ℓ) = Ef.card := by unfold cnt; congr
  rw [hcnt]
  have hfib : ∀ a ∈ Ef.image g, (Ef.filter fun R => g R = a).card ≤ n := by
    intro a ha
    obtain ⟨R0, hR0, rfl⟩ := Finset.mem_image.1 ha
    have hsame' : ∀ R S, g R = g S → R ∈ agreeOff I S := by
      intro R S hR i hi
      have := congrFun hR i
      simpa [hg, hi] using this
    have hsame : ∀ R, g R = g R0 → R ∈ agreeOff I R0 := fun R h => hsame' R R0 h
    have hmem : ∀ R ∈ Ef.filter (fun R => g R = g R0), blockX T R t ℓ ∈ delBall ((1:ℝ)/1000) ℓ (blockY T R0 t ℓ) := by
      intro R hR
      rw [Finset.mem_filter] at hR
      have hRE : R ∈ badEvent T t ℓ := by simpa [hEf] using hR.1
      refine ⟨blockX_length T R t ℓ ht, ?_⟩
      have := hY R0 R (hsame R hR.2)
      have h2 : (1 - (1:ℝ)/1000) * ℓ < (lcs (blockX T R t ℓ) (blockY T R t ℓ) : ℝ) := hRE
      rw [this] at h2; exact h2
    have hlen : (blockY T R0 t ℓ).length = ℓ := by
      simp only [blockY, factor, List.length_take, List.length_drop, W_length]; omega
    refine le_trans ?_ (hB _ hlen)
    rw [Set.ncard_eq_toFinset_card _ (delBall_finite _ _ _)]
    apply Finset.card_le_card_of_injOn (fun R => blockX T R t ℓ)
    · intro R hR; simpa using hmem R hR
    · intro R hR R' hR' hXX
      have hRf := Finset.mem_filter.1 hR
      have hRf' := Finset.mem_filter.1 hR'
      have hs' : R' ∈ agreeOff I R := hsame' R' R (hRf'.2.trans hRf.2.symm)
      have h1 := class_le_one I R {R'' | blockX T R'' t ℓ = blockX T R t ℓ} (fun i _ => rfl)
        (hX R _ (blockX_length T R t ℓ ht))
      unfold cnt at h1
      refine (Finset.card_le_one.1 h1 R ?_ R' ?_)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨rfl, fun i _ => rfl⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hXX.symm, hs'⟩
  have hcard := Finset.card_le_mul_card_image Ef n hfib
  have himg : (Ef.image g).card ≤ 2 ^ (T.length - I.card) := by
    rw [← G_card I]
    apply Finset.card_le_card
    intro a ha
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.1 ha
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i ∈ I <;> simp [hg, hi]
  calc Ef.card ≤ n * (Ef.image g).card := hcard
    _ ≤ n * 2 ^ (T.length - I.card) := Nat.mul_le_mul_left _ himg

theorem analytic (ℓ : ℝ) (hℓ : 1000 < ℓ) :
    Real.exp (9 * ℓ / 500) * (4 * Real.exp (-(Real.log 2 / 18) * ℓ)) ≤ Real.exp (-(9 * ℓ) / 500) := by
  have h4 : (4:ℝ) = Real.exp (2 * Real.log 2) := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [← this, Real.exp_log (by norm_num)]
  rw [h4, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hL : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hL.le) (by linarith : (0:ℝ) ≤ ℓ)]

end TernarySync.Dev.Eq14

namespace TernarySync.Alphabet
open TernarySync.Dev.Eq14 in
theorem chk_eq_14 (T : List (Fin 3)) (hT : IsSquareFree T) (t ℓ : ℕ) (hℓ : 1000 < ℓ)
    (ht : t + 2 * ℓ ≤ 18 * T.length) :
    unifProb (badEvent T t ℓ) < Real.exp (-(9 * (ℓ : ℝ)) / 500) := by
  obtain ⟨_, hall⟩ := TernarySync.Alphabet.lemma_4_2 T hT t ℓ hℓ ht
  have hℓ' : 1 < (1 : ℝ) / 1000 * (ℓ : ℝ) := by
    have : (1000 : ℝ) < ℓ := by exact_mod_cast hℓ
    linarith
  set S := (1 : ℝ) / 1000 * (ℓ : ℝ) *
    (Real.log 2 + 2 * Real.log (Real.exp 1 / ((1 : ℝ) / 1000)) + Real.log 3) with hS
  set n := ⌊Real.exp S⌋₊ with hn
  set I := completeBlocks T.length t ℓ with hI
  have hB : ∀ y : List (Fin 3), y.length = ℓ → (delBall ((1:ℝ)/1000) ℓ y).ncard ≤ n := by
    intro y hy
    exact Nat.le_floor (TernarySync.Alphabet.eq_12 ℓ hℓ' y hy).1
  have hcnt := count_bound T t ℓ n ht hB (fun f => (hall f).1)
    (fun f x hx => ((hall f).2 x hx).1)
  have hx0 : (List.replicate ℓ (0 : Fin 3)).length = ℓ := by simp
  have hnlt : (n : ℝ) < Real.exp (9 * (ℓ : ℝ) / 500) :=
    lt_of_le_of_lt (Nat.floor_le (Real.exp_pos S).le)
      (TernarySync.Alphabet.eq_12 ℓ hℓ' _ hx0).2
  have hc := ((hall (fun _ => 0)).2 _ hx0).2
  have hsN : I.card ≤ T.length := by
    calc I.card ≤ (Finset.univ : Finset (Fin T.length)).card := Finset.card_le_univ _
      _ = T.length := by simp
  have hprob : unifProb (badEvent T t ℓ) ≤ (n : ℝ) * (2 : ℝ) ^ (-(I.card : ℝ)) := by
    rw [unifProb_eq, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have h2N : (0:ℝ) < 2 ^ T.length := by positivity
    rw [div_le_iff₀ h2N]
    have hc' : (cnt (badEvent T t ℓ) : ℝ) ≤ n * 2 ^ (T.length - I.card) := by exact_mod_cast hcnt
    have hsplit : (2:ℝ) ^ T.length = 2 ^ (T.length - I.card) * 2 ^ I.card := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    have : (n : ℝ) * ((2:ℝ) ^ I.card)⁻¹ * (2 ^ (T.length - I.card) * 2 ^ I.card) =
        n * 2 ^ (T.length - I.card) := by
      field_simp
    rw [this]; exact hc'
  have hℓr : (1000 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hcpos : 0 < 4 * Real.exp (-(Real.log 2 / 18) * (ℓ : ℝ)) := by positivity
  calc unifProb (badEvent T t ℓ) ≤ (n : ℝ) * (2 : ℝ) ^ (-(I.card : ℝ)) := hprob
    _ ≤ (n : ℝ) * (4 * Real.exp (-(Real.log 2 / 18) * (ℓ : ℝ))) := by gcongr
    _ < Real.exp (9 * (ℓ : ℝ) / 500) * (4 * Real.exp (-(Real.log 2 / 18) * (ℓ : ℝ))) := by
        gcongr
    _ ≤ _ := analytic ℓ hℓr
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_eq_14 := @TernarySync.Alphabet.chk_eq_14

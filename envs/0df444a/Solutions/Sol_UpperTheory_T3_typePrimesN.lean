-- Prove2me | solution 1 for UpperTheory.T3.typePrimesN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:13.115248+00:00
-- url     : https://prove2.me/submissions/faef2013-5d31-4947-b127-ed34f992d694

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_normPrimesN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DivLeRpowThreeQuarters
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_typePrimesN
import Theorems.Thm_GlobalTheory_choice_count
import Theorems.Thm_UpperTheory_T3_normPrimesN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.Mem.An
namespace UpperTheory.T3
private theorem excluded_lt {Y r : ℝ} (hY : 1 ≤ Y) (hr : 1 ≤ r) (h : 20 * r ^ 3 < Y ^ ((3 : ℝ) / 20)) :
    (3 * r + 1) * (1 + 2 * r ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) < Y ^ ((9 : ℝ) / 10) := by
  have h34 : (1:ℝ) ≤ Y ^ ((3:ℝ)/4) := Real.one_le_rpow hY (by norm_num)
  have hsplit : Y ^ ((9:ℝ)/10) = Y ^ ((3:ℝ)/20) * Y ^ ((3:ℝ)/4) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hr2 : (1:ℝ) ≤ r ^ 2 := by nlinarith
  have a : 3 * r + 1 ≤ 4 * r := by linarith
  have b : 1 + 2 * r ^ 2 * (Y ^ ((3:ℝ)/4) + 1) ≤ 5 * r ^ 2 * Y ^ ((3:ℝ)/4) := by
    nlinarith [mul_le_mul_of_nonneg_left h34 (by linarith : (0:ℝ) ≤ r ^ 2)]
  have key : (3 * r + 1) * (1 + 2 * r ^ 2 * (Y ^ ((3:ℝ)/4) + 1)) ≤ 20 * r ^ 3 * Y ^ ((3:ℝ)/4) := by
    calc (3 * r + 1) * (1 + 2 * r ^ 2 * (Y ^ ((3:ℝ)/4) + 1))
        ≤ (4 * r) * (5 * r ^ 2 * Y ^ ((3:ℝ)/4)) :=
          mul_le_mul a b (by nlinarith) (by linarith)
      _ = 20 * r ^ 3 * Y ^ ((3:ℝ)/4) := by ring
  rw [hsplit]
  calc (3 * r + 1) * (1 + 2 * r ^ 2 * (Y ^ ((3:ℝ)/4) + 1))
      ≤ 20 * r ^ 3 * Y ^ ((3:ℝ)/4) := key
    _ < Y ^ ((3:ℝ)/20) * Y ^ ((3:ℝ)/4) := mul_lt_mul_of_pos_right h (by linarith)
private theorem exists_pair_disjoint {Y : ℝ} {r : ℕ} (hY : 2 ≤ Y) (hr : 1 ≤ r)
    (h : 20 * (r : ℝ) ^ 3 < Y ^ ((3 : ℝ) / 20)) (G : Finset ℕ) (hG : ∀ g ∈ G, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y)
    (hc : Y ^ ((9 : ℝ) / 10) ≤ G.card) :
    ∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ Disjoint (Formalism.CyclotomicNorms.BB r a) (Formalism.CyclotomicNorms.BB r b) := by
  by_contra hne
  push_neg at hne
  have hYpos : (0:ℝ) < Y := by linarith
  have hpos : (0:ℝ) < G.card := lt_of_lt_of_le (Real.rpow_pos_of_pos hYpos _) hc
  have hGne : G.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hpos
  obtain ⟨g₁, hg₁⟩ := hGne
  have hS := GlobalTheory.choice_count Y r g₁ hY (by exact_mod_cast hr) (hG g₁ hg₁).1 (hG g₁ hg₁).2 G (by
    intro g hg
    refine ⟨(hG g hg).1, (hG g hg).2, ?_⟩
    by_cases hgg : g = g₁
    · rw [hgg]
      exact ⟨g₁, by simp [Formalism.CyclotomicNorms.BB], by simp [Formalism.CyclotomicNorms.BB]⟩
    · exact Set.not_disjoint_iff_nonempty_inter.mp (hne g hg g₁ hg₁ hgg))
  have hlt := excluded_lt (by linarith) (by exact_mod_cast hr) h
  exact absurd (lt_of_le_of_lt hS hlt) (not_lt.mpr hc)
private theorem poly_le_exp (eps : ℝ) (he : 0 < eps) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, 1 ≤ x ∧ 21 * x ^ 15 ≤ Real.exp (x ^ eps) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 16 ≤ eps * n := by
    refine ⟨⌈16 / eps⌉₊, ?_⟩
    have := Nat.le_ceil (16 / eps)
    rw [div_le_iff₀ he] at this
    linarith
  refine ⟨21 * (n.factorial : ℝ), fun x hx => ?_⟩
  have hf : (1:ℝ) ≤ n.factorial := Nat.one_le_cast.mpr (Nat.factorial_pos n)
  have hx1 : 1 ≤ x := by linarith
  refine ⟨hx1, ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have h1 := Real.pow_div_factorial_le_exp (x := x ^ eps) (Real.rpow_nonneg hx0 eps) n
  have h2 : x ^ 16 ≤ (x ^ eps) ^ n := by
    rw [← Real.rpow_natCast (x ^ eps), ← Real.rpow_mul hx0, ← Real.rpow_natCast x 16]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hfpos : (0:ℝ) < n.factorial := by linarith
  have h3 : 21 * x ^ 15 ≤ x ^ 16 / n.factorial := by
    rw [le_div_iff₀ hfpos]
    have hx15 : 0 ≤ x ^ 15 := by positivity
    have e : x ^ 16 = x * x ^ 15 := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hx hx15]
  calc 21 * x ^ 15 ≤ x ^ 16 / n.factorial := h3
    _ ≤ (x ^ eps) ^ n / n.factorial := by gcongr
    _ ≤ Real.exp (x ^ eps) := h1
end UpperTheory.T3
end

set_option autoImplicit false
open GlobalTheory.Mem.An
open UpperTheory UpperTheory.T3
namespace UpperTheory.T3
theorem _root_.solution :
    ShortNorm → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ N d k r : ℕ, ModAt x eps N d → 1 ≤ k → 1 ≤ r → (r : ℝ) ≤ x ^ (5 : ℝ) →
      ∃ g : Fin 2 → ℕ, (∀ i, (g i).Prime ∧ ((k : ℝ) * Real.exp (x ^ eps)) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((k : ℝ) * Real.exp (x ^ eps)) ^ 8 ∧
        NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB r (g 0)) (Formalism.CyclotomicNorms.BB r (g 1)) := by
  intro hS eps he
  obtain ⟨x₁, hx₁⟩ := normPrimesN hS eps he
  obtain ⟨x₂, hx₂⟩ := poly_le_exp eps he
  refine ⟨max x₁ x₂, fun x hx N d k r hM hk hr hrx => ?_⟩
  have hx1 : x ≥ x₁ := le_trans (le_max_left _ _) hx
  have hx2 : x ≥ x₂ := le_trans (le_max_right _ _) hx
  obtain ⟨hxone, hpoly⟩ := hx₂ x hx2
  set E := Real.exp (x ^ eps) with hEdef
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hE1 : 1 ≤ E := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hkE : 1 ≤ (k:ℝ) * E := one_le_mul_of_one_le_of_one_le hk1 hE1
  have hEkE : E ≤ (k:ℝ) * E := le_mul_of_one_le_left (by linarith) hk1
  set Y := ((k:ℝ) * E) ^ 8 with hYdef
  have hkEY : (k:ℝ) * E ≤ Y := le_self_pow₀ hkE (by norm_num)
  have hx15 : (1:ℝ) ≤ x ^ 15 := one_le_pow₀ hxone
  have hY2 : 2 ≤ Y := by linarith
  have hY3 : (k:ℝ) * E ≤ Y ^ ((3:ℝ)/20) := by
    rw [hYdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    calc (k:ℝ) * E = ((k:ℝ) * E) ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hkE (by norm_num)
  have hr3 : (r:ℝ) ^ 3 ≤ x ^ 15 := by
    have h5 : (r:ℝ) ≤ x ^ 5 := by
      rw [← Real.rpow_natCast]
      exact_mod_cast hrx
    calc (r:ℝ) ^ 3 ≤ (x ^ 5) ^ 3 := pow_le_pow_left₀ (by positivity) h5 3
      _ = x ^ 15 := by ring
  have hsmall : 20 * (r:ℝ) ^ 3 < Y ^ ((3:ℝ)/20) := by linarith
  have hlog : 8 * x ^ eps ≤ Real.log Y := by
    rw [hYdef, Real.log_pow, Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith)), hEdef,
      Real.log_exp]
    have := Real.log_nonneg hk1
    push_cast
    linarith
  have hcard := hx₁ x hx1 N d hM Y (by linarith) hlog
  have hY0 : (0:ℝ) ≤ Y := by linarith
  have hmem : ∀ p ∈ normPrimes d N Y (2 * Y),
      p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2 * Y ∧ NormOne d N p := by
    intro p hp
    simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hpr, hn⟩ := hp
    exact ⟨hpr, ((Nat.floor_lt hY0).mp h1).le, (Nat.le_floor_iff (by linarith)).mp h2, hn⟩
  obtain ⟨a, ha, b, hb, hab, hdis⟩ := exists_pair_disjoint hY2 hr hsmall (normPrimes d N Y (2 * Y))
    (fun g hg => ⟨(hmem g hg).2.1, (hmem g hg).2.2.1⟩) hcard
  refine ⟨![a, b], ?_, by simpa using hab, by simpa using hdis⟩
  intro i
  fin_cases i
  · simpa using hmem a ha
  · simpa using hmem b hb
end UpperTheory.T3

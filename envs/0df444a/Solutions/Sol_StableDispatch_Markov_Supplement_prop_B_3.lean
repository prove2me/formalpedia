-- Prove2me | solution 1 for StableDispatch.Markov.Supplement.prop_B_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:37.051499+00:00
-- url     : https://prove2.me/submissions/64f4585d-e35e-464e-a883-47ecfd3d8e51

import Mathlib
import Definitions.Def_StableDispatch_Markov_Supplement_Policy

open StableDispatch
open StableDispatch.Markov
open StableDispatch.Markov.Supplement

open MeasureTheory Asymptotics Filter

theorem solution (c : ℕ → ℝ) (hc : c =o[atTop] (fun n : ℕ => Real.log n))
    (P : ∀ n : ℕ, 1 ≤ n → Policy n) (hsym : ∀ n (hn : 1 ≤ n), WeaklySymmetric (P n hn))
    (hmem : ∀ n (hn : 1 ≤ n), ((P n hn).memSize : ℝ) ≤ (2 : ℝ) ^ c n)
    (s : ℕ → ℝ) (hs : s =o[atTop] (fun n : ℕ => (n : ℝ))) :
    ∃ N : ℕ, ∀ n (hn : 1 ≤ n), N ≤ n →
      ∀ (m : Fin (P n hn).memSize) (S : Finset (Fin n)), (S.card : ℝ) ≤ s n →
      ∀ (q : Fin n → Queue), (∀ i k, 0 ≤ q i k) →
      ∀ (μ : Fin n → ℝ), (∀ i, 0 ≤ μ i) →
      ∀ (w : ℝ), 0 ≤ w →
      ∀ j ∉ S, ∀ j' ∉ S,
        unif {v | (P n hn).f2 m w (info S q μ) v = j} =
          unif {v | (P n hn).f2 m w (info S q μ) v = j'} := by
            classical
            have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hc' := hc.bound (show 0 < 1 / (2 * Real.log 2) by positivity)
            have hs' := hs.bound (show (0 : ℝ) < 1 / 4 by norm_num)
            have hev : ∀ᶠ n : ℕ in atTop, s n + 2 * (2 : ℝ) ^ c n < (n : ℝ) := by
              filter_upwards [hc', hs', eventually_ge_atTop 64] with n hcn hsn hn
              have hn64 : (64 : ℝ) ≤ n := by exact_mod_cast hn
              have hn0 : (0 : ℝ) < n := by linarith
              have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
              have hcupper : c n ≤ (1 / (2 * Real.log 2)) * Real.log (n : ℝ) := by
                simpa only [Real.norm_eq_abs, abs_of_nonneg hln] using (le_abs_self (c n)).trans hcn
              have hexp : 2 * (Real.log 2 * c n) ≤ Real.log (n : ℝ) := by
                have := (mul_le_mul_of_nonneg_left hcupper (show 0 ≤ 2 * Real.log 2 by positivity))
                field_simp at this
                nlinarith
              have hsq : ((2 : ℝ) ^ c n) ^ (2 : ℕ) ≤ (n : ℝ) := by
                rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), pow_two, ← Real.exp_add]
                have := Real.exp_le_exp.mpr hexp
                simpa only [two_mul, Real.exp_log hn0] using this
              have hp : 0 ≤ (2 : ℝ) ^ c n := Real.rpow_nonneg (by norm_num) _
              have hpupper : (2 : ℝ) ^ c n ≤ (n : ℝ) / 4 := by
                by_contra h
                have hx : 4 < (2 : ℝ) ^ c n := by linarith
                have := mul_nonneg (sub_nonneg.mpr hx.le) hp
                nlinarith
              have hsupper : s n ≤ (n : ℝ) / 4 := by
                have := (le_abs_self (s n)).trans hsn
                simp only [Real.norm_eq_abs, abs_of_nonneg hn0.le] at this
                linarith
              linarith
            obtain ⟨N, hN⟩ := eventually_atTop.1 hev
            refine ⟨N, ?_⟩
            intro n hn hnN m S hS q hq μ hμ w hw a ha b hb
            let d : Fin (P n hn).memSize → Fin n → ENNReal :=
              fun m j => unif {v | (P n hn).f2 m w (info S q μ) v = j}
            have hswap : ∀ x ∉ S, ∀ y ∉ S, ∃ m' : Fin (P n hn).memSize,
                ∀ j, d m' j = d m (Equiv.swap x y j) := by
              intro x hx y hy
              obtain ⟨σM, _, hσ⟩ := hsym n hn (Equiv.swap x y)
              refine ⟨σM m, ?_⟩
              have hfix : ∀ i ∈ S, Equiv.swap x y i = i := by
                intro i hi
                exact Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hx hi)
                  (by rintro rfl; exact hy hi)
              have hmap : S.map (Equiv.swap x y).toEmbedding = S := by
                ext i
                simp only [Finset.mem_map, Equiv.toEmbedding_apply]
                constructor
                · rintro ⟨k, hk, rfl⟩
                  simpa only [hfix k hk] using hk
                · intro hi
                  exact ⟨i, hi, hfix i hi⟩
              have hinfo : info (S.map (Equiv.swap x y).toEmbedding)
                  (q ∘ (Equiv.swap x y).symm) (μ ∘ (Equiv.swap x y).symm) = info S q μ := by
                rw [hmap]
                funext i
                by_cases hi : i ∈ S
                · simp [info, hi, Equiv.symm_swap, hfix i hi]
                · simp [info, hi]
              intro j
              have h := hσ m w hw S q μ hq hμ j
              rw [hinfo] at h
              simpa only [d, Equiv.swap_apply_eq_iff] using h.symm
            have hcard : ∀ x ∉ S,
                (Finset.univ.filter (fun j => j ∉ S ∧ d m j ≠ d m x)).card ≤ (P n hn).memSize := by
              intro x hx
              let T := Finset.univ.filter (fun j => j ∉ S ∧ d m j ≠ d m x)
              have hex : ∀ j : {j // j ∈ T}, ∃ m' : Fin (P n hn).memSize,
                  ∀ k, d m' k = d m (Equiv.swap x j.val k) := by
                intro j
                exact hswap x hx j.val (Finset.mem_filter.mp j.property).2.1
              choose f hf using hex
              have hinj : Function.Injective f := by
                intro j k hjk
                by_contra hne
                have hjkne : j.val ≠ k.val := by
                  intro heq
                  exact hne (Subtype.ext heq)
                have hj : d m j.val ≠ d m x := (Finset.mem_filter.mp j.property).2.2
                have hjx : j.val ≠ x := by rintro h; exact hj (congrArg (d m) h)
                have h1 := hf j j.val
                have h2 := hf k j.val
                rw [Equiv.swap_apply_right] at h1
                rw [Equiv.swap_apply_of_ne_of_ne hjx hjkne] at h2
                rw [hjk] at h1
                exact hj (h2.symm.trans h1)
              have h := Fintype.card_le_of_injective f hinj
              simpa only [Fintype.card_coe, Fintype.card_fin] using h
            by_contra hab
            change d m a ≠ d m b at hab
            have hca := hcard a ha
            have hcb := hcard b hb
            have hcover : Sᶜ ⊆
                (Finset.univ.filter (fun j => j ∉ S ∧ d m j ≠ d m a)) ∪
                (Finset.univ.filter (fun j => j ∉ S ∧ d m j ≠ d m b)) := by
              intro j hj
              have hjS : j ∉ S := Finset.mem_compl.mp hj
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases hja : d m j = d m a
              · exact Or.inr ⟨hjS, by rw [hja]; exact hab⟩
              · exact Or.inl ⟨hjS, hja⟩
            have hsize : n - S.card ≤ 2 * (P n hn).memSize := by
              have hh := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
              rw [Finset.card_compl, Fintype.card_fin] at hh
              omega
            have hScard : S.card ≤ n := by simpa using Finset.card_le_univ S
            have htotal : n ≤ S.card + 2 * (P n hn).memSize := by omega
            have htotalR : (n : ℝ) ≤ (S.card : ℝ) + 2 * ((P n hn).memSize : ℝ) := by exact_mod_cast htotal
            have hstrict := hN n hnN
            have hm := hmem n hn
            linarith

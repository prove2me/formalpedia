-- Prove2me | solution 1 for StableDispatch.Markov.Supplement.cor_B_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:27.410618+00:00
-- url     : https://prove2.me/submissions/4bfced52-f1ba-474a-ad18-a094f93c82d2

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
      ∀ (m : Fin (P n hn).memSize) (w : ℝ), 0 ≤ w →
      ∀ S : Finset (Fin n), (S.card : ℝ) ≤ s n →
      ∀ σ : Equiv.Perm (Fin n),
        unif {u | (P n hn).f1 m w u = S} =
          unif {u | (P n hn).f1 m w u = S.map σ.toEmbedding} := by
            have hc' : ∀ᶠ n : ℕ in atTop, c n * Real.log 2 < Real.log n := by
              filter_upwards [hc.def (by norm_num : (0:ℝ) < 1/2), eventually_ge_atTop 2] with n h1 h2
              have hn2 : (2:ℝ) ≤ n := by exact_mod_cast h2
              have hlog : 0 < Real.log n := Real.log_pos (by linarith)
              rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog] at h1
              have hl2 : Real.log 2 < 1 := by
                have := Real.log_two_lt_d9; linarith
              have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
              calc c n * Real.log 2 ≤ |c n| * Real.log 2 :=
                    mul_le_mul_of_nonneg_right (le_abs_self _) hl2'.le
                _ ≤ |c n| := mul_le_of_le_one_right (abs_nonneg _) hl2.le
                _ ≤ 1/2 * Real.log n := h1
                _ < Real.log n := by linarith
            have hs' : ∀ᶠ n : ℕ in atTop, s n ≤ (n:ℝ) - 2 := by
              filter_upwards [hs.def (by norm_num : (0:ℝ) < 1/2), eventually_ge_atTop 4] with n h1 h2
              have hn2 : (4:ℝ) ≤ n := by exact_mod_cast h2
              rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ n)] at h1
              have := le_abs_self (s n)
              linarith
            obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hc'.and (hs'.and (eventually_ge_atTop 5)))
            refine ⟨N, fun n hn hNn m w hw S hS σ => ?_⟩
            obtain ⟨h1, h2, h5⟩ := hN n hNn
            have hmemlt : (P n hn).memSize < n := by
              have hnpos : (0:ℝ) < n := by
                have : (5:ℝ) ≤ n := by exact_mod_cast h5
                linarith
              have : ((P n hn).memSize : ℝ) < n := lt_of_le_of_lt (hmem n hn) (by
                rw [Real.rpow_def_of_pos (by norm_num)]
                rw [← Real.exp_log hnpos]
                exact Real.exp_lt_exp.mpr (by linarith [mul_comm (Real.log 2) (c n)]))
              exact_mod_cast this
            have hScard : S.card + 2 ≤ n := by
              have : (S.card : ℝ) ≤ n - 2 := hS.trans h2
              have : (S.card:ℝ) + 2 ≤ n := by linarith
              exact_mod_cast this
            let Q := P n hn
            choose σM hσM using hsym n hn
            let d : Finset (Fin n) → ENNReal := fun T => unif {u | Q.f1 m w u = T}
            have key : ∀ (τ : Equiv.Perm (Fin n)) (A : Finset (Fin n)),
                (A.map τ.toEmbedding).map τ⁻¹.toEmbedding = A := by
              intro τ A; ext x; simp [Equiv.Perm.inv_def]
            have key2 : ∀ (τ : Equiv.Perm (Fin n)) (A : Finset (Fin n)),
                (A.map τ⁻¹.toEmbedding).map τ.toEmbedding = A := by
              intro τ A; ext x; simp [Equiv.Perm.inv_def]
            have hmul : ∀ (a b : Equiv.Perm (Fin n)) (A : Finset (Fin n)),
                A.map (a*b).toEmbedding = (A.map b.toEmbedding).map a.toEmbedding := by
              intro a b A; rw [Finset.map_map]; rfl
            have hpush : ∀ (τ : Equiv.Perm (Fin n)) (T : Finset (Fin n)),
                unif {u | (Q.f1 m w u).map τ.toEmbedding = T} = d (T.map τ⁻¹.toEmbedding) := by
              intro τ T
              show unif _ = unif _
              congr 1; ext u; simp only [Set.mem_ofPred_eq]
              constructor
              · rintro h; rw [← h, key]
              · rintro h; rw [h, key2]
            let H : Subgroup (Equiv.Perm (Fin n)) :=
              { carrier := {τ | ∀ T, d (T.map τ.toEmbedding) = d T}
                mul_mem' := by
                  intro a b ha hb T
                  simp only [Set.mem_ofPred_eq] at *
                  rw [hmul, ha, hb]
                one_mem' := by
                  intro T
                  have : T.map (1 : Equiv.Perm (Fin n)).toEmbedding = T := by ext x; rw [Finset.mem_map_equiv]; rfl
                  rw [this]
                inv_mem' := by
                  intro a ha T
                  simp only [Set.mem_ofPred_eq] at *
                  rw [← ha (T.map a⁻¹.toEmbedding), key2] }
            have hmemH : ∀ τ, τ ∈ H ↔ ∀ T, d (T.map τ.toEmbedding) = d T := fun τ => Iff.rfl
            have hidx : H.index ≤ Q.memSize := by
              let g : Equiv.Perm (Fin n) ⧸ H → Fin Q.memSize := fun q => σM q.out m
              have hg : Function.Injective g := by
                intro q1 q2 hq
                rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq]
                have e : ∀ T : Finset (Fin n), d (T.map ((q1.out : Equiv.Perm (Fin n))⁻¹).toEmbedding) = d (T.map ((q2.out : Equiv.Perm (Fin n))⁻¹).toEmbedding) := by
                  intro T
                  rw [← hpush, ← hpush, (hσM q1.out).1 m w hw T, (hσM q2.out).1 m w hw T]
                  simp only [g] at hq; rw [hq]
                rw [hmemH]
                intro T
                rw [hmul, e, key]
              have := Nat.card_le_card_of_injective g hg
              simpa [Subgroup.index] using this
            have hAH : alternatingGroup (Fin n) ≤ H := by
              by_cases hbot : H.normalCore = ⊥
              · exfalso
                have hinj : Function.Injective
                    (MulAction.toPermHom (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n) ⧸ H)) := by
                  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hbot]
                have hle := Nat.card_le_card_of_injective _ hinj
                rw [Nat.card_perm, Nat.card_perm, Nat.card_fin] at hle
                have h3 : Nat.card (Equiv.Perm (Fin n) ⧸ H) < n := lt_of_le_of_lt hidx hmemlt
                have hpos : 0 < Nat.card (Equiv.Perm (Fin n) ⧸ H) := Nat.card_pos
                have := (Nat.factorial_lt hpos).mpr h3
                omega
              · have hnt : Nontrivial H.normalCore := (Subgroup.nontrivial_iff_ne_bot _).mpr hbot
                have := H.normalCore_normal
                exact (Equiv.Perm.alternatingGroup_le_of_normal (by simp; omega) hnt).trans
                  (Subgroup.normalCore_le H)
            have hfin : ∀ τ ∈ alternatingGroup (Fin n), d (S.map τ.toEmbedding) = d S :=
              fun τ hτ => (hAH hτ) S
            show d S = d (S.map σ.toEmbedding)
            by_cases hσ : σ ∈ alternatingGroup (Fin n)
            · exact (hfin σ hσ).symm
            · obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ (Finset.univ \ S), ∃ b ∈ (Finset.univ \ S), a ≠ b := by
                rw [← Finset.one_lt_card]
                rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
                omega
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ha hb
              have hτ : σ * Equiv.swap a b ∈ alternatingGroup (Fin n) := by
                rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
                rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
                rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
                · exact absurd h hσ
                · rw [h]; decide
              have hsw : S.map (Equiv.swap a b).toEmbedding = S := by
                ext x
                rw [Finset.mem_map_equiv, Equiv.symm_swap]
                by_cases hx : x ∈ S
                · have hxa : x ≠ a := fun h => ha (h ▸ hx)
                  have hxb : x ≠ b := fun h => hb (h ▸ hx)
                  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
                · simp only [hx, iff_false]
                  intro hx'
                  by_cases hxa : x = a
                  · subst hxa; rw [Equiv.swap_apply_left] at hx'; exact hb hx'
                  · by_cases hxb : x = b
                    · subst hxb; rw [Equiv.swap_apply_right] at hx'; exact ha hx'
                    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb] at hx'; exact hx hx'
              rw [← hfin _ hτ, hmul, hsw]

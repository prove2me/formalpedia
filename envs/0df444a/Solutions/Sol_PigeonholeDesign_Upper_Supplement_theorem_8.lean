-- Prove2me | solution 1 for PigeonholeDesign.Upper.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:33.401147+00:00
-- url     : https://prove2.me/submissions/e9bcb017-9937-4523-ab7e-8f46f45c8abf

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

open PigeonholeDesign
open PigeonholeDesign.Upper
open PigeonholeDesign.Upper.Supplement

theorem solution (p q : ℕ) (hp : 2 ≤ p) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∃ x : Fin T → MultiDim.Cov q p, MultiDim.Admissible S x ∧
        c * (T : ℝ) ^ (((p : ℝ) - 1) / p) ≤ PigeonholeDesign.Upper.crdExp x := by
          classical
          refine ⟨1/4, by norm_num, 1, ?_⟩
          intro T hT hEven
          have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
          have hT1 : (1:ℝ) ≤ T := by exact_mod_cast hT
          set r : ℝ := (T:ℝ) ^ ((p:ℝ)⁻¹) with hr
          have hr1 : 1 ≤ r := Real.one_le_rpow hT1 (by positivity)
          set m : ℕ := ⌈r⌉₊ with hm
          have hmr : r ≤ (m:ℝ) := Nat.le_ceil r
          have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
            intro h; have := Nat.ceil_pos.mpr (show (0:ℝ) < r by linarith); omega)
          have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
          have hmr2 : (m:ℝ) ≤ 2 * r := by
            have := (Nat.ceil_lt_add_one (show (0:ℝ) ≤ r by linarith)).le
            linarith
          have hTm : T ≤ m ^ p := by
            have h1 : (T:ℝ) = r ^ p := by
              rw [hr]; exact (Real.rpow_inv_natCast_pow (by positivity) (by omega)).symm
            have h2 : r ^ p ≤ (m:ℝ) ^ p := pow_le_pow_left₀ (by linarith) hmr p
            exact_mod_cast (h1 ▸ h2 : (T:ℝ) ≤ (m:ℝ)^p)
          obtain ⟨e⟩ : Nonempty (Fin T ↪ (Fin p → Fin m)) :=
            Function.Embedding.nonempty_of_card_le (by simpa using hTm)
          let s : Fin q → ℝ := fun i => (hne i).choose
          let x : Fin T → MultiDim.Cov q p := fun t =>
            WithLp.toLp 2 (Sum.elim (fun i => s i) (fun j => ((e t j : ℕ) : ℝ) / m))
          have hsep : ∀ t t' : Fin T, t ≠ t' → 1 / (m:ℝ) ≤ dist (x t) (x t') := by
            intro t t' htt
            have : e t ≠ e t' := fun h => htt (e.injective h)
            obtain ⟨j, hj⟩ := Function.ne_iff.mp this
            refine le_trans ?_ (PiLp.dist_apply_le (x t) (x t') (Sum.inr j))
            simp only [x, Sum.elim_inr, Real.dist_eq]
            rw [← sub_div, abs_div, abs_of_pos hmpos]
            apply div_le_div_of_nonneg_right _ hmpos.le
            have : ((e t j : ℕ) : ℤ) ≠ ((e t' j : ℕ) : ℤ) := by
              intro h; apply hj; exact Fin.ext (by exact_mod_cast h)
            have h3 : (1:ℤ) ≤ |((e t j : ℕ) : ℤ) - ((e t' j : ℕ) : ℤ)| :=
              Int.one_le_abs (sub_ne_zero.mpr this)
            exact_mod_cast h3
          have hadm : MultiDim.Admissible S x := by
            refine ⟨fun t i => ?_, fun t j => ?_⟩
            · simp only [x, Sum.elim_inl]
              exact (hne i).choose_spec
            · simp only [x, Sum.elim_inr]
              refine ⟨by positivity, ?_⟩
              rw [div_le_one hmpos]
              exact_mod_cast (e t j).isLt.le
          refine ⟨x, hadm, ?_⟩
          set L : ℝ := ((T/2 : ℕ) : ℝ) / m with hL
          have hkey : ∀ V ∈ (Finset.univ : Finset (Fin T)).powersetCard (T / 2),
              L ≤ PigeonholeDesign.Upper.discrepancy x (fun t => decide (t ∉ V)) := by
            intro V hV
            rw [Finset.mem_powersetCard] at hV
            have hcF : Fintype.card {t // decide (t ∉ V) = false} = T / 2 := by
              rw [Fintype.card_subtype]
              rw [← hV.2]; congr 1; ext t; simp
            have hcT : Fintype.card {t // decide (t ∉ V) = true} = T / 2 := by
              rw [Fintype.card_subtype]
              have : (Finset.univ.filter fun t => decide (t ∉ V) = true) = Vᶜ := by ext t; simp
              rw [this, Finset.card_compl, hV.2, Fintype.card_fin]
              obtain ⟨k, hk⟩ := hEven; omega
            have : Nonempty ({t // decide (t ∉ V) = false} ≃ {t // decide (t ∉ V) = true}) :=
              ⟨Fintype.equivOfCardEq (hcF.trans hcT.symm)⟩
            unfold PigeonholeDesign.Upper.discrepancy
            apply le_ciInf
            intro f
            have : ∀ a : {t // decide (t ∉ V) = false}, 1 / (m:ℝ) ≤ dist (x a) (x (f a)) := by
              intro a
              apply hsep
              intro h
              have h1 : (a : Fin T) ∈ V := by simpa using a.2
              have h2 : ((f a : Fin T)) ∉ V := by simpa using (f a).2
              exact h2 (h ▸ h1)
            calc L = ∑ _a : {t // decide (t ∉ V) = false}, 1 / (m:ℝ) := by
                  rw [Finset.sum_const, Finset.card_univ, hcF, nsmul_eq_mul, hL]; ring
              _ ≤ _ := Finset.sum_le_sum (fun a _ => this a)
          have hcrd : L ≤ PigeonholeDesign.Upper.crdExp x := by
            unfold PigeonholeDesign.Upper.crdExp
            have hcpos : (0:ℝ) < (T.choose (T/2) : ℝ) := by
              exact_mod_cast Nat.choose_pos (Nat.div_le_self T 2)
            rw [le_div_iff₀ hcpos]
            have := Finset.card_nsmul_le_sum _ _ L hkey
            rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
            linarith
          refine le_trans ?_ hcrd
          have hT2 : ((T/2 : ℕ) : ℝ) = (T:ℝ) / 2 := by
            obtain ⟨k, hk⟩ := hEven
            subst hk
            rw [show (k + k) / 2 = k by omega]; push_cast; ring
          have hexp : (T:ℝ) ^ (((p : ℝ) - 1) / p) = (T:ℝ) / r := by
            rw [hr, show ((p:ℝ) - 1) / p = 1 - (p:ℝ)⁻¹ by field_simp,
              Real.rpow_sub (by linarith), Real.rpow_one]
          rw [hexp, hL, hT2]
          have hrpos : 0 < r := by linarith
          rw [div_div]
          have hT0 : (0:ℝ) ≤ T := by linarith
          calc 1/4 * ((T:ℝ) / r) = (T:ℝ) / (4 * r) := by ring
            _ ≤ (T:ℝ) / (2 * m) := div_le_div_of_nonneg_left hT0 (by positivity) (by linarith)

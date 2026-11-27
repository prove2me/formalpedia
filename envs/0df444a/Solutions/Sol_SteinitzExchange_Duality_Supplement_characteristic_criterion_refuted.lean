-- Prove2me | solution 1 for SteinitzExchange.Duality.Supplement.characteristic_criterion_refuted
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:55.767438+00:00
-- url     : https://prove2.me/submissions/014ad680-0eef-4634-9912-5ac67a109fac

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Conjugate
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization
import Definitions.Def_SteinitzExchange_Duality_Supplement_CharacteristicCounterexample

open SteinitzExchange
open SteinitzExchange.Duality
open SteinitzExchange.Duality.Supplement

/-- Refutation of the converse of printed Theorem 5.4, p. 293. The support
minimum's hypograph is the characteristic cone (p. 291). Both matroidality
conditions hold, on a nonempty hole-free integral base set, but (EXC) fails. -/
theorem solution :
    IsIntegralBaseSet characteristicBase ∧
    (∀ x : Fin 2 → ℤ, x ∈ characteristicBase ↔ toReal x ∈ hull characteristicBase) ∧
    (∀ p : Fin 2 → ℝ, concaveConj characteristicBase characteristicValue p =
      2 * min (p 0) (p 1)) ∧
    SteinitzExchange.LocalSupermod.IsMatroidal
      (SteinitzExchange.LocalSupermod.supportMin characteristicBase) ∧
    (∀ p₀ : Fin 2 → ℝ, SteinitzExchange.LocalSupermod.IsMatroidal
      (SteinitzExchange.LocalSupermod.localization
        (concaveConj characteristicBase characteristicValue) p₀)) ∧
    ¬ SatisfiesEXC characteristicBase characteristicValue := by
      classical
      have memB (x : Fin 2 → ℤ) : x ∈ characteristicBase ↔
          x = ![2, 0] ∨ x = ![1, 1] ∨ x = ![0, 2] := by
        simp [characteristicBase]
      have hbase : IsIntegralBaseSet characteristicBase := by
        refine ⟨⟨![2, 0], by simp [characteristicBase]⟩, ?_⟩
        intro x hx y hy u hu
        rw [memB] at hx hy
        rcases hx with rfl | rfl | rfl <;>
          rcases hy with rfl | rfl | rfl <;> fin_cases u <;>
          norm_num [Pi.sub_apply] at hu
        all_goals first
          | (solve | refine ⟨0, ?_, ?_⟩ <;> norm_num [chi, Pi.single_apply, Matrix.vecHead, Matrix.vecTail, Pi.sub_apply,
              Pi.add_apply, memB, funext_iff, Fin.forall_fin_two])
          | (solve | refine ⟨1, ?_, ?_⟩ <;> norm_num [chi, Pi.single_apply, Matrix.vecHead, Matrix.vecTail, Pi.sub_apply,
              Pi.add_apply, memB, funext_iff, Fin.forall_fin_two])
      have hhole : ∀ x : Fin 2 → ℤ,
          x ∈ characteristicBase ↔ toReal x ∈ hull characteristicBase := by
        intro x
        constructor
        · intro hx
          exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩
        · intro hx
          have hc : Convex ℝ {b : Fin 2 → ℝ | 0 ≤ b 0 ∧ 0 ≤ b 1 ∧ b 0 + b 1 = 2} := by
            intro a ha b hb s t hs ht hst
            dsimp at *
            refine ⟨add_nonneg (mul_nonneg hs ha.1) (mul_nonneg ht hb.1),
              add_nonneg (mul_nonneg hs ha.2.1) (mul_nonneg ht hb.2.1), ?_⟩
            nlinarith [ha.2.2, hb.2.2]
          have hs : hull characteristicBase ⊆
              {b : Fin 2 → ℝ | 0 ≤ b 0 ∧ 0 ≤ b 1 ∧ b 0 + b 1 = 2} := by
            apply convexHull_min ?_ hc
            rintro _ ⟨b, hb, rfl⟩
            change b ∈ characteristicBase at hb
            rw [memB] at hb
            rcases hb with rfl | rfl | rfl <;> norm_num [toReal]
          have hh := hs hx
          change 0 ≤ (x 0 : ℝ) ∧ 0 ≤ (x 1 : ℝ) ∧ (x 0 : ℝ) + (x 1 : ℝ) = 2 at hh
          have hi : 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 = 2 := by exact_mod_cast hh
          have hcases : x 0 = 2 ∨ x 0 = 1 ∨ x 0 = 0 := by omega
          rw [memB]
          rcases hcases with h | h | h
          · left; ext i; fin_cases i <;> simp_all <;> omega
          · right; left; ext i; fin_cases i <;> simp_all <;> omega
          · right; right; ext i; fin_cases i <;> simp_all <;> omega
      have hnot : ¬ SatisfiesEXC characteristicBase characteristicValue := by
        intro h
        obtain ⟨v, hv, _, _, hw⟩ := h ![2, 0] (by simp [characteristicBase])
          ![0, 2] (by simp [characteristicBase]) 0 (by norm_num)
        fin_cases v
        · norm_num at hv
        · norm_num [characteristicValue, chi, Pi.single_apply, Matrix.vecHead, Matrix.vecTail, funext_iff,
            Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply] at hw
      have hconj : ∀ p : Fin 2 → ℝ,
          concaveConj characteristicBase characteristicValue p = 2 * min (p 0) (p 1) := by
        intro p
        haveI : Nonempty (characteristicBase : Set (Fin 2 → ℤ)) :=
          ⟨⟨![2, 0], by simp [characteristicBase]⟩⟩
        have hlo : ∀ x : (characteristicBase : Set (Fin 2 → ℤ)),
            2 * min (p 0) (p 1) ≤ pairing p (toReal x) - characteristicValue x := by
          intro ⟨x, hx⟩
          change x ∈ characteristicBase at hx
          rw [memB] at hx
          rcases hx with rfl | rfl | rfl <;>
            norm_num [pairing, toReal, characteristicValue, Fin.sum_univ_two,
              funext_iff, Fin.forall_fin_two]
          all_goals nlinarith [min_le_left (p 0) (p 1), min_le_right (p 0) (p 1)]
        apply le_antisymm
        · have hb : BddBelow (Set.range (fun x : (characteristicBase : Set (Fin 2 → ℤ)) =>
              pairing p (toReal x) - characteristicValue x)) := ⟨_, by rintro _ ⟨x, rfl⟩; exact hlo x⟩
          by_cases hp : p 0 ≤ p 1
          · apply (ciInf_le hb ⟨![2, 0], by simp [characteristicBase]⟩).trans
            norm_num [pairing, toReal, characteristicValue, Fin.sum_univ_two,
              funext_iff, Fin.forall_fin_two, min_eq_left hp]
            linarith
          · apply (ciInf_le hb ⟨![0, 2], by simp [characteristicBase]⟩).trans
            norm_num [pairing, toReal, characteristicValue, Fin.sum_univ_two,
              funext_iff, Fin.forall_fin_two, min_eq_right (le_of_not_ge hp)]
            linarith
        · exact le_ciInf hlo
      have hsupp : ∀ p : Fin 2 → ℝ,
          SteinitzExchange.LocalSupermod.supportMin characteristicBase p = 2 * min (p 0) (p 1) := by
        intro p
        haveI : Nonempty (characteristicBase : Set (Fin 2 → ℤ)) :=
          ⟨⟨![2, 0], by simp [characteristicBase]⟩⟩
        change (⨅ x : (characteristicBase : Set (Fin 2 → ℤ)), pairing p (toReal x)) = _
        have hlo : ∀ x : (characteristicBase : Set (Fin 2 → ℤ)),
            2 * min (p 0) (p 1) ≤ pairing p (toReal x) := by
          intro ⟨x, hx⟩
          change x ∈ characteristicBase at hx
          rw [memB] at hx
          rcases hx with rfl | rfl | rfl <;>
            norm_num [pairing, toReal, Fin.sum_univ_two]
          all_goals nlinarith [min_le_left (p 0) (p 1), min_le_right (p 0) (p 1)]
        apply le_antisymm
        · have hb : BddBelow (Set.range (fun x : (characteristicBase : Set (Fin 2 → ℤ)) =>
              pairing p (toReal x))) := ⟨_, by rintro _ ⟨x, rfl⟩; exact hlo x⟩
          by_cases hp : p 0 ≤ p 1
          · apply (ciInf_le hb ⟨![2, 0], by simp [characteristicBase]⟩).trans
            norm_num [pairing, toReal, Fin.sum_univ_two, min_eq_left hp]
            linarith
          · apply (ciInf_le hb ⟨![0, 2], by simp [characteristicBase]⟩).trans
            norm_num [pairing, toReal, Fin.sum_univ_two, min_eq_right (le_of_not_ge hp)]
            linarith
        · exact le_ciInf hlo
      have hmat (a b c : ℝ) (hc : 0 ≤ c) :
          SteinitzExchange.LocalSupermod.IsMatroidal
            (fun p : Fin 2 → ℝ => a * p 0 + b * p 1 + c * min (p 0) (p 1)) := by
        refine ⟨?_, ?_, ?_⟩
        · intro t ht p
          dsimp
          rw [← mul_min_of_nonneg (p 0) (p 1) (le_of_lt ht)]
          ring
        · intro X Y
          dsimp [SteinitzExchange.LocalSupermod.charVec]
          by_cases hx0 : (0 : Fin 2) ∈ X <;> by_cases hx1 : (1 : Fin 2) ∈ X <;>
            by_cases hy0 : (0 : Fin 2) ∈ Y <;> by_cases hy1 : (1 : Fin 2) ∈ Y <;>
            norm_num [hx0, hx1, hy0, hy1, Finset.mem_union, Finset.mem_inter] <;> linarith
        · change ∀ (p : Fin 2 → ℝ) (σ : Fin 2 ≃ Fin 2), Antitone (p ∘ σ) →
            a * p 0 + b * p 1 + c * min (p 0) (p 1) =
              ∑ j : Fin 2,
                (p (σ j) - (if hj : (j : ℕ) + 1 < 2 then p (σ ⟨(j : ℕ) + 1, hj⟩) else 0)) *
                  (a * (SteinitzExchange.LocalSupermod.charVec
                      (Finset.univ.filter (fun v => σ.symm v ≤ j))) 0 +
                   b * (SteinitzExchange.LocalSupermod.charVec
                      (Finset.univ.filter (fun v => σ.symm v ≤ j))) 1 +
                   c * min ((SteinitzExchange.LocalSupermod.charVec
                      (Finset.univ.filter (fun v => σ.symm v ≤ j))) 0)
                     ((SteinitzExchange.LocalSupermod.charVec
                      (Finset.univ.filter (fun v => σ.symm v ≤ j))) 1))
          intro p σ hp
          have hσ : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
            have hn : σ 0 ≠ σ 1 := fun h => by have := σ.injective h; norm_num at this
            have hx : σ 0 = 0 ∨ σ 0 = 1 := by omega
            have hy : σ 1 = 0 ∨ σ 1 = 1 := by omega
            rcases hx with h0 | h0 <;> rcases hy with h1 | h1 <;> simp_all
          have hord := hp (show (0 : Fin 2) ≤ 1 by decide)
          rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · have hs0 : σ.symm 0 = 0 := by apply σ.injective; simp [h0]
            have hs1 : σ.symm 1 = 1 := by apply σ.injective; simp [h1]
            have hh : p 1 ≤ p 0 := by simpa [Function.comp_def, h0, h1] using hord
            simp [Fin.sum_univ_two, SteinitzExchange.LocalSupermod.charVec, h0, h1,
              hs0, hs1, min_eq_right hh]
            ring
          · have hs0 : σ.symm 0 = 1 := by apply σ.injective; simp [h1]
            have hs1 : σ.symm 1 = 0 := by apply σ.injective; simp [h0]
            have hh : p 0 ≤ p 1 := by simpa [Function.comp_def, h0, h1] using hord
            simp [Fin.sum_univ_two, SteinitzExchange.LocalSupermod.charVec, h0, h1,
              hs0, hs1, min_eq_left hh]
            ring
      have hmatmin : SteinitzExchange.LocalSupermod.IsMatroidal
          (fun p : Fin 2 → ℝ => 2 * min (p 0) (p 1)) := by
        simpa using hmat 0 0 2 (by norm_num)
      have hmatsupp : SteinitzExchange.LocalSupermod.IsMatroidal
          (SteinitzExchange.LocalSupermod.supportMin characteristicBase) := by
        convert hmatmin using 1
        exact funext hsupp
      let F : (Fin 2 → ℝ) → ℝ := fun p => 2 * min (p 0) (p 1)
      have hsd (p₀ b : Fin 2 → ℝ)
          (hb : b ∈ SteinitzExchange.LocalSupermod.superdiff F p₀) :
          0 ≤ b 0 ∧ 0 ≤ b 1 ∧ b 0 + b 1 = 2 ∧
            p₀ 0 * b 0 + p₀ 1 * b 1 = 2 * min (p₀ 0) (p₀ 1) := by
        have hi (q : Fin 2 → ℝ) : 2 * min (q 0) (q 1) - 2 * min (p₀ 0) (p₀ 1) ≤
            (q 0 - p₀ 0) * b 0 + (q 1 - p₀ 1) * b 1 := by
          simpa [F, SteinitzExchange.LocalSupermod.pairing, Fin.sum_univ_two] using hb q
        have he : p₀ 0 * b 0 + p₀ 1 * b 1 = 2 * min (p₀ 0) (p₀ 1) := by
          have hz := hi ![0, 0]
          have ht := hi ![2 * p₀ 0, 2 * p₀ 1]
          have hm : min (2 * p₀ 0) (2 * p₀ 1) = 2 * min (p₀ 0) (p₀ 1) :=
            (mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)).symm
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hm] at hz ht
          norm_num at hz
          nlinarith
        have hall (q : Fin 2 → ℝ) : 2 * min (q 0) (q 1) ≤ q 0 * b 0 + q 1 * b 1 := by
          have hh := hi q
          nlinarith [he]
        have h0 := hall ![1, 0]
        have h1 := hall ![0, 1]
        have hp := hall ![1, 1]
        have hn := hall ![-1, -1]
        norm_num at h0 h1 hp hn
        exact ⟨h0, h1, by linarith, he⟩
      have hend0 (p₀ : Fin 2 → ℝ) (hp : p₀ 0 ≤ p₀ 1) :
          (![2, 0] : Fin 2 → ℝ) ∈ SteinitzExchange.LocalSupermod.superdiff F p₀ := by
        intro q
        have hh := min_le_left (q 0) (q 1)
        simp [F, SteinitzExchange.LocalSupermod.pairing, Fin.sum_univ_two, min_eq_left hp]
        linarith
      have hend1 (p₀ : Fin 2 → ℝ) (hp : p₀ 1 ≤ p₀ 0) :
          (![0, 2] : Fin 2 → ℝ) ∈ SteinitzExchange.LocalSupermod.superdiff F p₀ := by
        intro q
        have hh := min_le_right (q 0) (q 1)
        simp [F, SteinitzExchange.LocalSupermod.pairing, Fin.sum_univ_two, min_eq_right hp]
        linarith
      have hinf (p₀ q : Fin 2 → ℝ) (z : ℝ)
          (hlo : ∀ b ∈ SteinitzExchange.LocalSupermod.superdiff F p₀,
            z ≤ SteinitzExchange.LocalSupermod.pairing q b)
          (hw : ∃ b ∈ SteinitzExchange.LocalSupermod.superdiff F p₀,
            SteinitzExchange.LocalSupermod.pairing q b = z) :
          SteinitzExchange.LocalSupermod.localization F p₀ q = z := by
        have hz : z ∈ (fun b => SteinitzExchange.LocalSupermod.pairing q b) ''
            SteinitzExchange.LocalSupermod.superdiff F p₀ := by
          rcases hw with ⟨b, hb, he⟩
          exact ⟨b, hb, he⟩
        have hbound : ∀ r ∈ (fun b => SteinitzExchange.LocalSupermod.pairing q b) ''
            SteinitzExchange.LocalSupermod.superdiff F p₀, z ≤ r := by
          rintro r ⟨b, hb, rfl⟩
          exact hlo b hb
        exact le_antisymm (csInf_le ⟨z, hbound⟩ hz) (le_csInf ⟨z, hz⟩ hbound)
      have hloc0 (p₀ : Fin 2 → ℝ) (hp : p₀ 0 < p₀ 1) :
          SteinitzExchange.LocalSupermod.localization F p₀ = (fun q => 2 * q 0) := by
        funext q
        apply hinf
        · intro b hb
          rcases hsd p₀ b hb with ⟨hb0, hb1, hsum, he⟩
          rw [min_eq_left hp.le] at he
          have hz : (p₀ 1 - p₀ 0) * b 1 = 0 := by
            nlinarith [congrArg (fun r : ℝ => p₀ 0 * r) hsum]
          have h1 : b 1 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr hp))
          have h0 : b 0 = 2 := by linarith
          simp [SteinitzExchange.LocalSupermod.pairing, Fin.sum_univ_two, h0, h1]
          linarith
        · refine ⟨![2, 0], hend0 p₀ hp.le, ?_⟩
          simp [SteinitzExchange.LocalSupermod.pairing, Fin.sum_univ_two]
          ring
      have hloc1 (p₀ : Fin 2 → ℝ) (hp : p₀ 1 < p₀ 0) :
          SteinitzExchange.LocalSupermod.localization F p₀ = (fun q => 2 * q 1) := by
        funext q
        apply hinf
        · intro b hb
          rcases hsd p₀ b hb with ⟨hb0, hb1, hsum, he⟩
          rw [min_eq_right hp.le] at he
          have hz : (p₀ 0 - p₀ 1) * b 0 = 0 := by
            nlinarith [congrArg (fun r : ℝ => p₀ 1 * r) hsum]
          have h0 : b 0 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr hp))
          have h1 : b 1 = 2 := by linarith
          simp [SteinitzExchange.LocalSupermod.pairing, Fin.sum_univ_two, h0, h1]
          linarith
        · refine ⟨![0, 2], hend1 p₀ hp.le, ?_⟩
          simp [SteinitzExchange.LocalSupermod.pairing, Fin.sum_univ_two]
          ring
      have hloceq (p₀ : Fin 2 → ℝ) (hp : p₀ 0 = p₀ 1) :
          SteinitzExchange.LocalSupermod.localization F p₀ = F := by
        funext q
        apply hinf
        · intro b hb
          rcases hsd p₀ b hb with ⟨hb0, hb1, hsum, he⟩
          dsimp [F, SteinitzExchange.LocalSupermod.pairing]
          rw [Fin.sum_univ_two]
          have h0 := mul_nonneg (sub_nonneg.mpr (min_le_left (q 0) (q 1))) hb0
          have h1 := mul_nonneg (sub_nonneg.mpr (min_le_right (q 0) (q 1))) hb1
          nlinarith [congrArg (fun r : ℝ => min (q 0) (q 1) * r) hsum]
        · by_cases hq : q 0 ≤ q 1
          · refine ⟨![2, 0], hend0 p₀ hp.le, ?_⟩
            simp [F, SteinitzExchange.LocalSupermod.pairing, Fin.sum_univ_two, min_eq_left hq]
            ring
          · refine ⟨![0, 2], hend1 p₀ hp.ge, ?_⟩
            simp [F, SteinitzExchange.LocalSupermod.pairing, Fin.sum_univ_two,
              min_eq_right (le_of_not_ge hq)]
            ring
      refine ⟨hbase, hhole, hconj, hmatsupp, ?_, hnot⟩
      intro p₀
      have hF : concaveConj characteristicBase characteristicValue = F := funext hconj
      rw [hF]
      rcases lt_trichotomy (p₀ 0) (p₀ 1) with hp | hp | hp
      · rw [hloc0 p₀ hp]
        simpa using hmat 2 0 0 (by norm_num)
      · rw [hloceq p₀ hp]
        exact hmatmin
      · rw [hloc1 p₀ hp]
        simpa using hmat 0 2 0 (by norm_num)

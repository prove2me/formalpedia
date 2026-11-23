-- Prove2me | solution 1 for VecKnapsackMitM.Main.lemma_4_8
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:27:58.687803+00:00
-- url     : https://prove2.me/submissions/2eb7c180-a05f-4cf1-a3a6-fb6b213d117c

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_VirtualItem
import Definitions.Def_VecKnapsackMitM_Main_Convolution

namespace Aux48

open VecKnapsackMitM.Main MatMulTimeLP

lemma isVItem_unique {d n : ℕ} {I : Items d n} {s : State} {a : ℕ}
    {v₁ v₂ : Finset (Fin n)} (h₁ : IsVItem I s a v₁) (h₂ : IsVItem I s a v₂) :
    v₁ = v₂ := by
  obtain ⟨⟨vis₁, nod₁, hw₁, _, _, hmem₁, _⟩, _⟩ := h₁
  obtain ⟨⟨vis₂, nod₂, hw₂, _, _, hmem₂, _⟩, _⟩ := h₂
  rw [hw₁] at hw₂
  have hnod : nod₁ = nod₂ := (Prod.ext_iff.mp (Option.some.inj hw₂)).2
  subst hnod
  ext x
  exact (hmem₁ x).trans (hmem₂ x).symm

lemma mem_eq_of_length_le_one {α : Type*} {l : List α} (hl : l.length ≤ 1)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) : x = y := by
  rcases l with _ | ⟨a, _ | ⟨b, tl⟩⟩
  · simp at hx
  · simp only [List.mem_singleton] at hx hy
    exact hx.trans hy.symm
  · simp only [List.length_cons] at hl
    omega

lemma bound_lt_two (C : ℝ) (hC : 0 < C) :
    let M : ℝ := 8 * C + 4
    let η : ℝ := (2 : ℝ) ^ (-(1 / M))
    let ε : ℝ := 1 / (1 + 1 / M)
    0 < ε ∧ ε < 1 ∧ 0 < η ∧ η < 1 ∧
      (Real.logb 2 (NN 2 / η) / ε) ^ (C * (2 : ℝ)) < 2 := by
  intro M η ε
  have hM : 4 < M := by dsimp [M]; linarith
  have hMpos : 0 < M := by linarith
  have h1M_pos : 0 < 1 / M := div_pos one_pos hMpos
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := by
    dsimp [ε]
    rw [div_lt_one (by linarith)]
    linarith
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hη1 : η < 1 := by
    dsimp [η]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos h1M_pos)
  refine ⟨hε0, hε1, hη0, hη1, ?_⟩
  have hNN : NN 2 = 2 := by unfold NN; norm_num
  have hdiv : NN 2 / η = (2 : ℝ) ^ (1 + 1 / M) := by
    rw [hNN]
    dsimp [η]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  have hlog : Real.logb 2 (NN 2 / η) = 1 + 1 / M := by
    rw [hdiv, Real.logb_rpow (by norm_num) (by norm_num)]
  have hbase : Real.logb 2 (NN 2 / η) / ε = (1 + 1 / M) ^ (2 : ℝ) := by
    rw [hlog]
    dsimp [ε]
    rw [div_div_eq_mul_div, div_one, Real.rpow_two]
    ring
  have hrpow : (Real.logb 2 (NN 2 / η) / ε) ^ (C * (2 : ℝ)) = (1 + 1 / M) ^ (4 * C) := by
    rw [hbase, ← Real.rpow_mul (by linarith)]
    ring_nf
  rw [hrpow]
  have hexp1 : 1 + 1 / M ≤ Real.exp (1 / M) := by linarith [Real.add_one_le_exp (1 / M)]
  have hexp2 : (1 + 1 / M) ^ (4 * C) ≤ (Real.exp (1 / M)) ^ (4 * C) :=
    Real.rpow_le_rpow (by linarith) hexp1 (by linarith)
  have hexp3 : (Real.exp (1 / M)) ^ (4 * C) = Real.exp (4 * C / M) := by
    rw [← Real.exp_mul]
    ring_nf
  have hfrac : 4 * C / M < 1 / 2 := by
    rw [div_lt_iff₀ hMpos]
    dsimp [M]
    linarith
  have hexp_half : Real.exp (1 / 2) < 2 := by
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have he1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
    nlinarith
  calc (1 + 1 / M) ^ (4 * C)
      ≤ Real.exp (4 * C / M) := hexp2.trans_eq hexp3
    _ < Real.exp (1 / 2) := Real.exp_lt_exp.mpr hfrac
    _ < 2 := hexp_half

end Aux48

open VecKnapsackMitM.Main MatMulTimeLP

theorem solution :
    ¬ (∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ), 2 ≤ d → ∀ I : Items d n, I.Nonneg →
        ∀ Wt : Fin d → ℝ, (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → 0 ≤ Wt t) →
        ∀ (ε η : ℝ), 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 →
          RunsWithin P (sec45Input I Wt ε η)
            (C * NN n * (Real.logb 2 (NN n / η) / ε) ^ (C * (d : ℝ)))
            (fun s => ∀ i : Fin n,
              ((listAt s (s.N (2 + i.val))).length : ℝ) ≤
                (Real.logb 2 (NN n / η) / ε) ^ (C * (d : ℝ)) ∧
              (∀ a ∈ listAt s (s.N (2 + i.val)),
                ∃ S, IsVItem I s a S ∧ S ⊆ Items.suffix n i.val) ∧
              ∀ Q ⊆ Items.suffix n i.val,
                η * Items.maxOver (Items.suffix n i.val) I.p ≤ I.profit Q →
                (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → I.weight Q t ≤ Wt t / η) →
                ∃ a ∈ listAt s (s.N (2 + i.val)), ∃ v, IsVItem I s a v ∧
                  (1 - ε) * I.profit Q ≤ I.profit v ∧
                  (∀ t : Fin d, t.val = 0 → I.weight v t ≤
                    max ((1 + ε) * I.weight Q t)
                      (η * Items.maxOver (Items.suffix n i.val) I.w1)) ∧
                  (∀ t : Fin d, t.val + 1 = d → I.weight v t ≤ I.weight Q t) ∧
                  ∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d →
                    I.weight v t ≤ max ((1 + ε) * I.weight Q t) (η * Wt t))) := by
  rintro ⟨P, _, C, hC, hAll⟩
  obtain ⟨hε0, hε1, hη0, hη1, hlt2⟩ := Aux48.bound_lt_two C hC
  let M : ℝ := 8 * C + 4
  let η : ℝ := (2 : ℝ) ^ (-(1 / M))
  let ε : ℝ := 1 / (1 + 1 / M)
  let I : Items 2 2 :=
    { p := fun _ => 1
      w := fun i t => if i.val = t.val then 1 else 0 }
  have hI : I.Nonneg := by
    refine ⟨fun _ => by norm_num [I], fun i t => ?_⟩
    dsimp [I]
    split_ifs <;> norm_num
  let Wt : Fin 2 → ℝ := fun _ => 0
  have hWt : ∀ t : Fin 2, 1 ≤ t.val → t.val + 2 ≤ 2 → 0 ≤ Wt t := fun _ _ _ => le_rfl
  obtain ⟨t, _, _, hOut⟩ := hAll 2 2 (by omega) I hI Wt hWt ε η hε0 hε1.le hη0 hη1.le
  let i0 : Fin 2 := ⟨0, by omega⟩
  let i1 : Fin 2 := ⟨1, by omega⟩
  obtain ⟨hlen_real, _, hQ⟩ := hOut i0
  have hlen_lt : ((listAt (run P (sec45Input I Wt ε η) t)
      ((run P (sec45Input I Wt ε η) t).N 2)).length : ℝ) < 2 :=
    lt_of_le_of_lt hlen_real hlt2
  have hlen_nat : (listAt (run P (sec45Input I Wt ε η) t)
      ((run P (sec45Input I Wt ε η) t).N 2)).length ≤ 1 := by
    have hlt_nat : (listAt (run P (sec45Input I Wt ε η) t)
        ((run P (sec45Input I Wt ε η) t).N 2)).length < 2 := by exact_mod_cast hlen_lt
    omega
  have hsuf : Items.suffix 2 0 = Finset.univ := by
    ext j
    simp [Items.suffix]
  have hmaxP : Items.maxOver (Items.suffix 2 0) I.p = 1 := by
    rw [hsuf]
    unfold Items.maxOver
    rw [dif_pos Finset.univ_nonempty]
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun _ _ => le_rfl
    · exact Finset.le_sup' I.p (Finset.mem_univ i0)
  have hmaxW1 : Items.maxOver (Items.suffix 2 0) I.w1 = 1 := by
    rw [hsuf]
    unfold Items.maxOver
    rw [dif_pos Finset.univ_nonempty]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j _ => ?_
      simp only [Items.w1, Nat.zero_lt_two, ↓reduceDIte, I]
      split_ifs <;> norm_num
    · have hi0w : I.w1 i0 = 1 := by simp [Items.w1, I, i0]
      rw [← hi0w]
      exact Finset.le_sup' I.w1 (Finset.mem_univ i0)
  -- Apply to Q₁ = {i0}
  have hQ1_sub : ({i0} : Finset (Fin 2)) ⊆ Items.suffix 2 0 := by simp [hsuf]
  have hQ1_prof : η * Items.maxOver (Items.suffix 2 0) I.p ≤ I.profit {i0} := by
    rw [hmaxP]
    simp only [Items.profit, Finset.sum_singleton, I]
    linarith
  have hQ1_mid : ∀ t : Fin 2, 1 ≤ t.val → t.val + 2 ≤ 2 → I.weight {i0} t ≤ Wt t / η := by
    intro t ht1 ht2; omega
  obtain ⟨a₁, ha₁, v₁, hv₁, hv₁_prof, _, hv₁_last, _⟩ := hQ {i0} hQ1_sub hQ1_prof hQ1_mid
  -- Apply to Q₂ = {i1}
  have hQ2_sub : ({i1} : Finset (Fin 2)) ⊆ Items.suffix 2 0 := by simp [hsuf]
  have hQ2_prof : η * Items.maxOver (Items.suffix 2 0) I.p ≤ I.profit {i1} := by
    rw [hmaxP]
    simp only [Items.profit, Finset.sum_singleton, I]
    linarith
  have hQ2_mid : ∀ t : Fin 2, 1 ≤ t.val → t.val + 2 ≤ 2 → I.weight {i1} t ≤ Wt t / η := by
    intro t ht1 ht2; omega
  obtain ⟨a₂, ha₂, v₂, hv₂, _, hv₂_first, _, _⟩ := hQ {i1} hQ2_sub hQ2_prof hQ2_mid
  -- Deduce v₁ = v₂
  have ha_eq : a₁ = a₂ := Aux48.mem_eq_of_length_le_one hlen_nat ha₁ ha₂
  rw [ha_eq] at hv₁
  have hv_eq : v₁ = v₂ := Aux48.isVItem_unique hv₁ hv₂
  -- Show i0 ∈ v₁
  have hv₁_nonempty : v₁.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hv₁_prof
    simp only [Items.profit, Finset.sum_singleton, Finset.sum_empty, I] at hv₁_prof
    linarith
  have hi1_not_v₁ : i1 ∉ v₁ := by
    intro hmem
    have hw_le := hv₁_last i1 rfl
    have hw_q1 : I.weight {i0} i1 = 0 := by simp [Items.weight, I, i0, i1]
    have hw_ge : (1 : ℝ) ≤ I.weight v₁ i1 := by
      have h1 : I.w i1 i1 = 1 := by simp [I, i1]
      rw [← h1]
      exact Finset.single_le_sum (fun j _ => hI.2 j i1) hmem
    linarith
  obtain ⟨j, hj⟩ := hv₁_nonempty
  have hj_eq : j = i0 := by
    fin_cases j
    · rfl
    · exact False.elim (hi1_not_v₁ hj)
  have hi0_in_v₂ : i0 ∈ v₂ := by rw [← hv_eq, ← hj_eq]; exact hj
  -- Show i0 ∉ v₂, contradiction
  have hw2_le := hv₂_first i0 rfl
  have hw_q2 : I.weight {i1} i0 = 0 := by simp [Items.weight, I, i0, i1]
  rw [hw_q2, mul_zero, hmaxW1, mul_one, max_eq_right hη0.le] at hw2_le
  have hw2_ge : (1 : ℝ) ≤ I.weight v₂ i0 := by
    have h1 : I.w i0 i0 = 1 := by simp [I, i0]
    rw [← h1]
    exact Finset.single_le_sum (fun j _ => hI.2 j i0) hi0_in_v₂
  linarith

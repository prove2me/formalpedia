-- Prove2me | solution 1 for VecKnapsackMitM.Main.claim_4_13
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:32:20.720711+00:00
-- url     : https://prove2.me/submissions/b656f2b3-1181-4919-9284-6fe9bb82e65d

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_Convolution

namespace Aux413

open VecKnapsackMitM.Main MatMulTimeLP

lemma step_N_finset (P : Program) (ω : Tape) (t : ℕ) (s : State) (V : Finset ℕ)
    (hV : ∀ m, s.N m ∈ V) :
    ∃ V' : Finset ℕ, V'.card ≤ V.card + 1 ∧ ∀ m, (step P ω t s).N m ∈ V' := by
  unfold step
  cases P[s.pc]? with
  | none => exact ⟨V, Nat.le_succ _, hV⟩
  | some ins =>
    cases ins with
    | halt => exact ⟨V, Nat.le_succ _, hV⟩
    | rconst _ _ => exact ⟨V, Nat.le_succ _, hV⟩
    | radd _ _ _ => exact ⟨V, Nat.le_succ _, hV⟩
    | rsub _ _ _ => exact ⟨V, Nat.le_succ _, hV⟩
    | rmul _ _ _ => exact ⟨V, Nat.le_succ _, hV⟩
    | rdiv _ _ _ => exact ⟨V, Nat.le_succ _, hV⟩
    | rsqrt _ _ => exact ⟨V, Nat.le_succ _, hV⟩
    | rload _ _ => exact ⟨V, Nat.le_succ _, hV⟩
    | rstore _ _ => exact ⟨V, Nat.le_succ _, hV⟩
    | gauss _ => exact ⟨V, Nat.le_succ _, hV⟩
    | unif _ => exact ⟨V, Nat.le_succ _, hV⟩
    | rblt i j l =>
      by_cases hlt : s.R i < s.R j <;> simp [hlt] <;> exact ⟨V, Nat.le_succ _, hV⟩
    | nblt i j l =>
      by_cases hlt : s.N i < s.N j <;> simp [hlt] <;> exact ⟨V, Nat.le_succ _, hV⟩
    | nconst i k =>
      refine ⟨insert k V, Finset.card_insert_le _ _, fun m => ?_⟩
      by_cases hm : m = i
      · subst hm; simp
      · simp [Function.update_of_ne hm, hV m]
    | nadd i j k =>
      refine ⟨insert (s.N j + s.N k) V, Finset.card_insert_le _ _, fun m => ?_⟩
      by_cases hm : m = i
      · subst hm; simp
      · simp [Function.update_of_ne hm, hV m]
    | nsub i j k =>
      refine ⟨insert (s.N j - s.N k) V, Finset.card_insert_le _ _, fun m => ?_⟩
      by_cases hm : m = i
      · subst hm; simp
      · simp [Function.update_of_ne hm, hV m]
    | nload i j =>
      refine ⟨insert (s.N (s.N j)) V, Finset.card_insert_le _ _, fun m => ?_⟩
      by_cases hm : m = i
      · subst hm; simp
      · simp [Function.update_of_ne hm, hV m]
    | nstore i j =>
      refine ⟨insert (s.N j) V, Finset.card_insert_le _ _, fun m => ?_⟩
      by_cases hm : m = s.N i
      · subst hm; simp
      · simp [Function.update_of_ne hm, hV m]

lemma run_N_finset (P : Program) (s₀ : State) (V₀ : Finset ℕ) (hV₀ : ∀ m, s₀.N m ∈ V₀) :
    ∀ t : ℕ, ∃ V : Finset ℕ, V.card ≤ V₀.card + t ∧ ∀ m, (run P s₀ t).N m ∈ V
  | 0 => ⟨V₀, by simp, hV₀⟩
  | t + 1 => by
    obtain ⟨V, hVc, hVm⟩ := run_N_finset P s₀ V₀ hV₀ t
    obtain ⟨V', hV'c, hV'm⟩ := step_N_finset P zeroTape t (run P s₀ t) V hVm
    exact ⟨V', by omega, hV'm⟩

lemma inGrid_zero_one :
    InGrid (cDelta 2 1) (cBigDelta 2 1 1) (cBigDelta 2 1 1) 0 ∧
    InGrid (cDelta 2 1) (cBigDelta 2 1 1) (cBigDelta 2 1 1) 1 := by
  refine ⟨Or.inl rfl, Or.inr ⟨?_, ?_, 0, by norm_num⟩⟩
  · unfold cBigDelta; norm_num
  · unfold cBigDelta; norm_num

def boolVec (d : ℕ) (hd : 2 ≤ d) (b : Fin d → Bool) : PVec d :=
  { prof := if b ⟨d - 1, by omega⟩ then 1 else 0
    wt := fun j => if j.val + 1 < d then (if b j then 1 else 0) else 0 }

lemma boolVec_injective (d : ℕ) (hd : 2 ≤ d) : Function.Injective (boolVec d hd) := by
  intro b₁ b₂ h
  have hp : (boolVec d hd b₁).prof = (boolVec d hd b₂).prof := congrArg PVec.prof h
  have hw : ∀ j, (boolVec d hd b₁).wt j = (boolVec d hd b₂).wt j := congrFun (congrArg PVec.wt h)
  ext j
  by_cases hj : j.val + 1 < d
  · have hjw := hw j
    simp only [boolVec, hj, ↓reduceIte] at hjw
    cases hb₁ : b₁ j <;> cases hb₂ : b₂ j <;> simp [hb₁, hb₂] at hjw ⊢
  · have hjeq : j = ⟨d - 1, by omega⟩ := by
      apply Fin.ext
      simp only []
      have := j.isLt
      omega
    rw [hjeq]
    simp only [boolVec] at hp
    cases hb₁ : b₁ ⟨d - 1, by omega⟩ <;> cases hb₂ : b₂ ⟨d - 1, by omega⟩ <;> simp [hb₁, hb₂] at hp ⊢

lemma boolVec_inDom (d : ℕ) (hd : 2 ≤ d)
    (I : Items d 2) (hIp : I.p = fun _ => 1) (hIw : I.w = fun _ _ => 1)
    (Wt : Fin d → ℝ) (hWt : Wt = fun _ => 1)
    (J : Finset (Fin 2)) (hJ : J.Nonempty) (b : Fin d → Bool) :
    InDom I Wt 1 1 J (boolVec d hd b) := by
  have hmaxP : Items.maxOver J I.p = 1 := by
    unfold Items.maxOver
    rw [dif_pos hJ]
    obtain ⟨j₀, hj₀⟩ := hJ
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j _ => by simp [hIp]
    · have : I.p j₀ = 1 := by simp [hIp]
      rw [← this]
      exact Finset.le_sup' I.p hj₀
  have hmaxW1 : Items.maxOver J I.w1 = 1 := by
    unfold Items.maxOver
    rw [dif_pos hJ]
    obtain ⟨j₀, hj₀⟩ := hJ
    have hd0 : 0 < d := by omega
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j _ => by simp [Items.w1, hd0, hIw]
    · have : I.w1 j₀ = 1 := by simp [Items.w1, hd0, hIw]
      rw [← this]
      exact Finset.le_sup' I.w1 hj₀
  have hscP : scaleP I 1 1 J = cBigDelta 2 1 1 := by simp [scaleP, hmaxP]
  have hscW : ∀ t : Fin d, scaleW I Wt 1 1 J t = cBigDelta 2 1 1 := by
    intro t
    unfold scaleW
    split_ifs <;> simp [hmaxW1, hWt]
  obtain ⟨hg0, hg1⟩ := inGrid_zero_one
  refine ⟨?_, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · rw [hscP]
    dsimp [boolVec]
    split_ifs <;> assumption
  · rw [hscW t]
    dsimp [boolVec]
    rw [if_pos ht]
    split_ifs <;> assumption
  · dsimp [boolVec]
    have hnot : ¬ t.val + 1 < d := by omega
    rw [if_neg hnot]

end Aux413

open VecKnapsackMitM.Main MatMulTimeLP

theorem solution :
    ¬ (∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n k : ℕ), 2 ≤ d → n = 2 ^ k → 1 ≤ k → ∀ I : Items d n, I.Nonneg →
      ∀ Wt : Fin d → ℝ, (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → 0 ≤ Wt t) →
      ∀ (ε η : ℝ), 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 →
        RunsWithin P (sec45Input I Wt ε η)
          (C * n * (Real.logb 2 ((n : ℝ) / η) / ε) ^ (C * (d : ℝ)))
          (fun s => ∀ α β : ℕ, α ≤ k → 1 ≤ β → β ≤ 2 ^ (k - α) →
            ∃ f : AFun d n, TableRep I Wt ε η s (s.N (blockSlot k α β)) (block n α β) f ∧
              IsApproxOn I Wt ε η α (block n α β) f)) := by
  rintro ⟨P, _, C, hC, hAll⟩
  let d : ℕ := max 2 (Nat.ceil (2 * C) + 4)
  have hd : 2 ≤ d := le_max_left _ _
  have hd_gt : Nat.ceil (2 * C) + 4 ≤ d := le_max_right _ _
  let I : Items d 2 := ⟨fun _ => 1, fun _ _ => 1⟩
  have hI : I.Nonneg := ⟨fun _ => by norm_num, fun _ _ => by norm_num⟩
  let Wt : Fin d → ℝ := fun _ => 1
  obtain ⟨t, _, ht_bound, hOut⟩ :=
    hAll d 2 1 hd (by norm_num) (by omega) I hI Wt (fun _ _ _ => by norm_num)
      1 1 zero_lt_one le_rfl zero_lt_one le_rfl
  have hbound_eq : C * ((2 : ℕ) : ℝ) * (Real.logb 2 (((2 : ℕ) : ℝ) / 1) / 1) ^ (C * (d : ℝ)) = 2 * C := by
    push_cast
    have hlog : Real.logb 2 ((2 : ℝ) / 1) = 1 := by
      rw [div_one]
      exact Real.logb_self_eq_one (by norm_num)
    rw [hlog, div_one, Real.one_rpow]
    ring
  rw [hbound_eq] at ht_bound
  have ht_ceil : t ≤ Nat.ceil (2 * C) :=
    Nat.cast_le.mp ((by linarith : (t : ℝ) ≤ 2 * C).trans (Nat.le_ceil (2 * C)))
  obtain ⟨f, hTab, _⟩ := hOut 0 1 (by omega) (by omega) (by norm_num)
  let s₀ := sec45Input I Wt 1 1
  let s := run P s₀ t
  let V₀ : Finset ℕ := {0, d, 2}
  have hV₀ : ∀ m, s₀.N m ∈ V₀ := by
    intro m
    dsimp [s₀, sec45Input, initState2, ShadowBootstrap.initState2]
    rcases m with _ | _ | m <;> simp [V₀]
  obtain ⟨V, hVcard, hVmem⟩ := Aux413.run_N_finset P s₀ V₀ hV₀ t
  have hV₀_card : V₀.card ≤ 3 := by
    dsimp [V₀]
    exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
  have hJ_nonempty : (block 2 0 1).Nonempty := ⟨⟨0, by omega⟩, by simp [block]⟩
  classical
  let B : Finset (PVec d) := Finset.univ.image (Aux413.boolVec d hd)
  have hB_card : B.card = 2 ^ d := by
    rw [Finset.card_image_of_injective _ (Aux413.boolVec_injective d hd), Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  let K : Finset (PVec d) := V.image (keyAt s d)
  have hB_sub_K : B ⊆ K := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨b, _, rfl⟩ := hx
    have hdom := Aux413.boolVec_inDom d hd I rfl rfl Wt rfl (block 2 0 1) hJ_nonempty b
    have hmem_list := (hTab.2.1 _).mp hdom
    rw [List.mem_map] at hmem_list
    obtain ⟨e, he_in, he_eq⟩ := hmem_list
    rw [← he_eq]
    refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
    unfold listAt at he_in
    rw [List.mem_map] at he_in
    obtain ⟨j, _, rfl⟩ := he_in
    exact hVmem _
  have hcard_le : 2 ^ d ≤ 3 + t := by
    calc 2 ^ d = B.card := hB_card.symm
      _ ≤ K.card := Finset.card_le_card hB_sub_K
      _ ≤ V.card := Finset.card_image_le
      _ ≤ V₀.card + t := hVcard
      _ ≤ 3 + t := by omega
  have hd_lt_pow : d < 2 ^ d := Nat.lt_pow_self (by norm_num)
  omega

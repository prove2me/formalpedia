-- Prove2me | solution 1 for VecKnapsackMitM.Main.claim_4_11
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:48:26.151866+00:00
-- url     : https://prove2.me/submissions/a7db3fb5-ecc3-48cb-9fe2-ab91d63325ca

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_VirtualItem
import Definitions.Def_VecKnapsackMitM_Main_Convolution

namespace Aux411

open VecKnapsackMitM.Main MatMulTimeLP

def zeroPVec (d : ℕ) : PVec d := ⟨0, fun _ => 0⟩

lemma inGrid_zero_iff (δ Δ y : ℝ) : InGrid δ Δ 0 y ↔ y = 0 := by
  unfold InGrid
  constructor
  · rintro (rfl | ⟨_, h1, _⟩)
    · rfl
    · rw [mul_zero] at h1
      linarith
  · intro hy; exact Or.inl hy

lemma inDom_iff_zero (d : ℕ) (hd : 2 ≤ d)
    (I : Items d 2) (hIp : I.p = fun _ => 0) (hIw0 : ∀ i, I.w i ⟨0, by omega⟩ = 0)
    (Wt : Fin d → ℝ) (hWt : Wt = fun _ => 0)
    (J : Finset (Fin 2)) (x : PVec d) :
    InDom I Wt 1 1 J x ↔ x = zeroPVec d := by
  have hmaxP : Items.maxOver J I.p = 0 := by
    unfold Items.maxOver
    split_ifs with hJ
    · obtain ⟨j₀, hj₀⟩ := hJ
      apply le_antisymm
      · exact Finset.sup'_le _ _ fun j _ => by simp [hIp]
      · have : I.p j₀ = 0 := by simp [hIp]
        rw [← this]
        exact Finset.le_sup' I.p hj₀
    · rfl
  have hmaxW1 : Items.maxOver J I.w1 = 0 := by
    unfold Items.maxOver
    have hd0 : 0 < d := by omega
    split_ifs with hJ
    · obtain ⟨j₀, hj₀⟩ := hJ
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun j _ => ?_
        simp [Items.w1, hd0, hIw0 j]
      · have : I.w1 j₀ = 0 := by simp [Items.w1, hd0, hIw0 j₀]
        rw [← this]
        exact Finset.le_sup' I.w1 hj₀
    · rfl
  have hscP : scaleP I 1 1 J = 0 := by simp [scaleP, hmaxP]
  have hscW : ∀ t : Fin d, scaleW I Wt 1 1 J t = 0 := by
    intro t
    unfold scaleW
    split_ifs <;> simp [hmaxW1, hWt]
  constructor
  · rintro ⟨hp, hw⟩
    rw [hscP, inGrid_zero_iff] at hp
    cases x with
    | mk xp xw =>
      dsimp [zeroPVec] at hp ⊢
      congr 1
      ext t
      by_cases ht : t.val + 1 < d
      · have hwt := (hw t).1 ht
        rw [hscW t, inGrid_zero_iff] at hwt
        exact hwt
      · have hteq : t.val + 1 = d := by have := t.isLt; omega
        exact (hw t).2 hteq
  · rintro rfl
    refine ⟨?_, fun t => ⟨fun _ => ?_, fun _ => rfl⟩⟩
    · rw [hscP, inGrid_zero_iff]; rfl
    · rw [hscW t, inGrid_zero_iff]; rfl

lemma step_R_eq_two_finset (P : Program) (ω : Tape) (t : ℕ) (s : State) (W : Finset ℕ)
    (hW : ∀ m, s.R m = 2 → m ∈ W) :
    ∃ W' : Finset ℕ, W'.card ≤ W.card + 1 ∧ ∀ m, (step P ω t s).R m = 2 → m ∈ W' := by
  unfold step
  cases P[s.pc]? with
  | none => exact ⟨W, Nat.le_succ _, hW⟩
  | some ins =>
    cases ins with
    | halt => exact ⟨W, Nat.le_succ _, hW⟩
    | nconst _ _ => exact ⟨W, Nat.le_succ _, hW⟩
    | nadd _ _ _ => exact ⟨W, Nat.le_succ _, hW⟩
    | nsub _ _ _ => exact ⟨W, Nat.le_succ _, hW⟩
    | nload _ _ => exact ⟨W, Nat.le_succ _, hW⟩
    | nstore _ _ => exact ⟨W, Nat.le_succ _, hW⟩
    | rblt i j l =>
      by_cases hlt : s.R i < s.R j <;> simp [hlt] <;> exact ⟨W, Nat.le_succ _, hW⟩
    | nblt i j l =>
      by_cases hlt : s.N i < s.N j <;> simp [hlt] <;> exact ⟨W, Nat.le_succ _, hW⟩
    | rconst i _ =>
      refine ⟨insert i W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)
    | radd i _ _ =>
      refine ⟨insert i W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)
    | rsub i _ _ =>
      refine ⟨insert i W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)
    | rmul i _ _ =>
      refine ⟨insert i W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)
    | rdiv i _ _ =>
      refine ⟨insert i W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)
    | rsqrt i _ =>
      refine ⟨insert i W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)
    | rload i _ =>
      refine ⟨insert i W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)
    | rstore i _ =>
      refine ⟨insert (s.N i) W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = s.N i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)
    | gauss i =>
      refine ⟨insert i W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)
    | unif i =>
      refine ⟨insert i W, Finset.card_insert_le _ _, fun m hm => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      · simp only [Function.update_of_ne hmi] at hm
        exact Finset.mem_insert_of_mem (hW m hm)

lemma run_R_eq_two_finset (P : Program) (s₀ : State) (h₀ : ∀ m, s₀.R m ≠ 2) :
    ∀ t : ℕ, ∃ W : Finset ℕ, W.card ≤ t ∧ ∀ m, (run P s₀ t).R m = 2 → m ∈ W
  | 0 => ⟨∅, le_rfl, fun m hm => False.elim (h₀ m hm)⟩
  | t + 1 => by
    obtain ⟨W, hWc, hWm⟩ := run_R_eq_two_finset P s₀ h₀ t
    obtain ⟨W', hW'c, hW'm⟩ := step_R_eq_two_finset P zeroTape t (run P s₀ t) W hWm
    exact ⟨W', by omega, hW'm⟩

lemma walk_leaf (s : State) (fuel a code : ℕ) (hf : 1 ≤ fuel) (ha : a ≠ 0)
    (hc : s.N a = code) (h0 : code ≠ 0) (hl : s.N (a + 1) = 0) (hr : s.N (a + 2) = 0) :
    walk s fuel a = some ([code - 1], [a]) := by
  rcases fuel with _ | f
  · omega
  · simp [walk, ha, hc, h0, hl, hr]

def mkInitR (d : ℕ) (m : ℕ) : ℝ :=
  let vA := 6 + d + 4 + 2 * (d + 1)
  let vB := vA + (d + 3)
  if m = 0 ∨ m = 1 then 1
  else if vA + 2 ≤ m ∧ m < vA + 1 + d then 1
  else if vB + 2 ≤ m ∧ m < vB + 1 + d then 1
  else 0

def mkInitN (d : ℕ) : ℕ → ℕ :=
  let tbA := 6 + d
  let tbB := 6 + d + 2
  let eA := 6 + d + 4
  let eB := 6 + d + 4 + (d + 1)
  let vA := 6 + d + 4 + 2 * (d + 1)
  let vB := vA + (d + 3)
  let F := vB + (d + 3)
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update (fun _ => 0) vB 2)
                          vA 1)
                        eB vB)
                      eA vA)
                    (tbB + 1) eB)
                  tbB 1)
                (tbA + 1) eA)
              tbA 1)
            4 F)
          3 tbB)
        2 tbA)
      1 2)
    0 d

def mkInitState (d : ℕ) : State := ⟨0, mkInitR d, mkInitN d⟩

lemma mkInitN_0 (d : ℕ) : (mkInitState d).N 0 = d := by
  dsimp [mkInitState, mkInitN]; rw [Function.update_apply, if_pos rfl]
lemma mkInitN_1 (d : ℕ) : (mkInitState d).N 1 = 2 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_2 (d : ℕ) : (mkInitState d).N 2 = 6 + d := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_3 (d : ℕ) : (mkInitState d).N 3 = 6 + d + 2 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_4 (d : ℕ) : (mkInitState d).N 4 = 6 + d + 4 + 2 * (d + 1) + (d + 3) + (d + 3) := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_tbA (d : ℕ) : (mkInitState d).N (6 + d) = 1 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_tbA1 (d : ℕ) : (mkInitState d).N (6 + d + 1) = 6 + d + 4 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_tbB (d : ℕ) : (mkInitState d).N (6 + d + 2) = 1 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_tbB1 (d : ℕ) : (mkInitState d).N (6 + d + 2 + 1) = 6 + d + 4 + (d + 1) := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_eA (d : ℕ) : (mkInitState d).N (6 + d + 4) = 6 + d + 4 + 2 * (d + 1) := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_eB (d : ℕ) :
    (mkInitState d).N (6 + d + 4 + (d + 1)) = 6 + d + 4 + 2 * (d + 1) + (d + 3) := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_vA (d : ℕ) : (mkInitState d).N (6 + d + 4 + 2 * (d + 1)) = 1 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_vA1 (d : ℕ) : (mkInitState d).N (6 + d + 4 + 2 * (d + 1) + 1) = 0 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
lemma mkInitN_vA2 (d : ℕ) : (mkInitState d).N (6 + d + 4 + 2 * (d + 1) + 2) = 0 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
lemma mkInitN_vB (d : ℕ) : (mkInitState d).N (6 + d + 4 + 2 * (d + 1) + (d + 3)) = 2 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
  rw [Function.update_apply, if_pos rfl]
lemma mkInitN_vB1 (d : ℕ) : (mkInitState d).N (6 + d + 4 + 2 * (d + 1) + (d + 3) + 1) = 0 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])
lemma mkInitN_vB2 (d : ℕ) : (mkInitState d).N (6 + d + 4 + 2 * (d + 1) + (d + 3) + 2) = 0 := by
  dsimp [mkInitState, mkInitN]; repeat (rw [Function.update_apply, if_neg (by omega)])

lemma mkInitR_no2 (d m : ℕ) : (mkInitState d).R m ≠ 2 := by
  dsimp [mkInitState, mkInitR]; split_ifs <;> norm_num

lemma mkInitR_zero_below_vA2 (d m : ℕ) (h1 : 2 ≤ m) (h2 : m < 6 + d + 4 + 2 * (d + 1) + 2) :
    (mkInitState d).R m = 0 := by
  dsimp [mkInitState, mkInitR]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma mkInitR_vA_wt (d : ℕ) (t : Fin d) :
    (mkInitState d).R (6 + d + 4 + 2 * (d + 1) + 1 + t.val) = if t.val = 0 then 0 else 1 := by
  have ht := t.isLt
  by_cases ht0 : t.val = 0
  · rw [if_pos ht0]
    exact mkInitR_zero_below_vA2 d _ (by omega) (by omega)
  · rw [if_neg ht0]
    dsimp [mkInitState, mkInitR]
    rw [if_neg (by omega), if_pos (by omega)]

lemma mkInitR_vB_zero (d : ℕ) :
    (mkInitState d).R (6 + d + 4 + 2 * (d + 1) + (d + 3)) = 0 := by
  dsimp [mkInitState, mkInitR]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma mkInitR_vB_wt (d : ℕ) (t : Fin d) :
    (mkInitState d).R (6 + d + 4 + 2 * (d + 1) + (d + 3) + 1 + t.val) =
      if t.val = 0 then 0 else 1 := by
  have ht := t.isLt
  by_cases ht0 : t.val = 0
  · rw [if_pos ht0]
    dsimp [mkInitState, mkInitR]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg ht0]
    dsimp [mkInitState, mkInitR]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

end Aux411

open VecKnapsackMitM.Main MatMulTimeLP

theorem solution :
    ¬ ((∀ (d n k : ℕ), 2 ≤ d → n = 2 ^ k → 1 ≤ k → ∀ I : Items d n, I.Nonneg →
        ∀ Wt : Fin d → ℝ, (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → 0 ≤ Wt t) →
        ∀ (ε η : ℝ), 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 →
        ∀ (A B : Finset (Fin n)), A.Nonempty → B.Nonempty → Disjoint A B →
        ∀ (α β : ℝ) (f g h : AFun d n),
          IsApproxOn I Wt ε η α A f → IsApproxOn I Wt ε η β B g → max α β + 1 ≤ (k : ℝ) →
          IsConv I Wt ε η A B f g h → IsApproxOn I Wt ε η (max α β + 1) (A ∪ B) h) ∧
      (∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (d n k : ℕ), 2 ≤ d → n = 2 ^ k → 1 ≤ k → ∀ I : Items d n, I.Nonneg →
        ∀ Wt : Fin d → ℝ, (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → 0 ≤ Wt t) →
        ∀ (ε η : ℝ), 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 →
        ∀ (A B : Finset (Fin n)), A.Nonempty → B.Nonempty → Disjoint A B →
        ∀ f g : AFun d n, IsAFun I Wt ε η A f → IsAFun I Wt ε η B g →
        ∀ s₀ : State, ConvInput I Wt ε η A B f g s₀ →
          RunsWithin P s₀ (C * (Real.logb 2 ((n : ℝ) / η) / ε) ^ (C * (d : ℝ)))
            (fun s => ∃ h : AFun d n, IsConv I Wt ε η A B f g h ∧
              TableRep I Wt ε η s (s.N 5) (A ∪ B) h))) := by
  rintro ⟨_, P, _, C, hC, hAll⟩
  let d : ℕ := Nat.ceil C + 4
  have hd : 2 ≤ d := by dsimp [d]; omega
  let i0 : Fin 2 := ⟨0, by omega⟩
  let i1 : Fin 2 := ⟨1, by omega⟩
  let I : Items d 2 :=
    { p := fun _ => 0
      w := fun _ t => if t.val = 0 then 0 else 1 }
  have hI : I.Nonneg := by
    refine ⟨fun _ => le_rfl, fun _ t => ?_⟩
    dsimp [I]; split_ifs <;> norm_num
  let Wt : Fin d → ℝ := fun _ => 0
  let A : Finset (Fin 2) := {i0}
  let B : Finset (Fin 2) := {i1}
  let f : AFun d 2 := fun _ => some A
  let g : AFun d 2 := fun _ => some B
  have hfA : IsAFun I Wt 1 1 A f := by
    intro _ _ S hS; injection hS with hEq; rw [← hEq]
  have hgB : IsAFun I Wt 1 1 B g := by
    intro _ _ S hS; injection hS with hEq; rw [← hEq]
  let s₀ : State := Aux411.mkInitState d
  let vA : ℕ := 6 + d + 4 + 2 * (d + 1)
  let vB : ℕ := vA + (d + 3)
  have hIw0 : ∀ i, I.w i ⟨0, by omega⟩ = 0 := fun _ => by simp [I]
  have hvA_walk : walk s₀ 5 vA = some ([0], [vA]) :=
    Aux411.walk_leaf s₀ 5 vA 1 (by omega) (by dsimp [vA]; omega)
      (Aux411.mkInitN_vA d) (by omega) (Aux411.mkInitN_vA1 d) (Aux411.mkInitN_vA2 d)
  have hvA_vitem : IsVItem I s₀ vA A := by
    have hroot : VItemRoot I s₀ vA A := by
      refine ⟨[0], [vA], hvA_walk, ?_⟩
      have hN : s₀.N vA = 1 := Aux411.mkInitN_vA d
      have hR0 : s₀.R vA = 0 := Aux411.mkInitR_zero_below_vA2 d vA (by dsimp [vA]; omega) (by dsimp [vA]; omega)
      refine ⟨by simp [hN], ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc; simp [hN] at hc; try omega
      · intro j; simp [A, i0, hN]; try omega
      · simp [A]
      · simp [hR0, Items.profit, A, I]
      · intro t
        simp only [Items.weight, A, Finset.sum_singleton, I]
        exact Aux411.mkInitR_vA_wt d t
    refine ⟨hroot, fun vis nod hwn u hu => ?_⟩
    rw [hvA_walk] at hwn
    have hnod : nod = [vA] := (Prod.ext_iff.mp (Option.some.inj hwn.symm)).2
    subst hnod
    simp only [List.mem_singleton] at hu; subst hu
    exact ⟨A, hroot⟩
  have hvB_walk : walk s₀ 5 vB = some ([1], [vB]) :=
    Aux411.walk_leaf s₀ 5 vB 2 (by omega) (by dsimp [vB, vA]; omega)
      (Aux411.mkInitN_vB d) (by omega) (Aux411.mkInitN_vB1 d) (Aux411.mkInitN_vB2 d)
  have hvB_vitem : IsVItem I s₀ vB B := by
    have hroot : VItemRoot I s₀ vB B := by
      refine ⟨[1], [vB], hvB_walk, ?_⟩
      have hN : s₀.N vB = 2 := Aux411.mkInitN_vB d
      have hR0 : s₀.R vB = 0 := Aux411.mkInitR_vB_zero d
      refine ⟨by simp [hN], ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc; simp [hN] at hc; try omega
      · intro j; simp [B, i1, hN]; try omega
      · simp [B]
      · simp [hR0, Items.profit, B, I]
      · intro t
        simp only [Items.weight, B, Finset.sum_singleton, I]
        exact Aux411.mkInitR_vB_wt d t
    refine ⟨hroot, fun vis nod hwn u hu => ?_⟩
    rw [hvB_walk] at hwn
    have hnod : nod = [vB] := (Prod.ext_iff.mp (Option.some.inj hwn.symm)).2
    subst hnod
    simp only [List.mem_singleton] at hu; subst hu
    exact ⟨B, hroot⟩
  have hlistA : listAt s₀ (6 + d) = [6 + d + 4] := by
    simp [listAt, s₀, Aux411.mkInitN_tbA d, Aux411.mkInitN_tbA1 d]
  have hlistB : listAt s₀ (6 + d + 2) = [6 + d + 4 + (d + 1)] := by
    simp [listAt, s₀, Aux411.mkInitN_tbB d, Aux411.mkInitN_tbB1 d]
  have hkeyA : keyAt s₀ d (6 + d + 4) = Aux411.zeroPVec d := by
    unfold keyAt Aux411.zeroPVec
    congr 1
    · exact Aux411.mkInitR_zero_below_vA2 d _ (by omega) (by omega)
    · ext t; split_ifs with ht
      · exact Aux411.mkInitR_zero_below_vA2 d _ (by omega) (by omega)
      · rfl
  have hkeyB : keyAt s₀ d (6 + d + 4 + (d + 1)) = Aux411.zeroPVec d := by
    unfold keyAt Aux411.zeroPVec
    congr 1
    · exact Aux411.mkInitR_zero_below_vA2 d _ (by omega) (by omega)
    · ext t; split_ifs with ht
      · exact Aux411.mkInitR_zero_below_vA2 d _ (by omega) (by omega)
      · rfl
  have hConv : ConvInput I Wt 1 1 A B f g s₀ := by
    have hmaxAP : Items.maxOver A I.p = 0 := by simp [Items.maxOver, A, I]
    have hmaxAW : Items.maxOver A I.w1 = 0 := by
      have hd0 : 0 < d := by omega
      simp [Items.maxOver, A, Items.w1, hd0, I]
    have hmaxBP : Items.maxOver B I.p = 0 := by simp [Items.maxOver, B, I]
    have hmaxBW : Items.maxOver B I.w1 = 0 := by
      have hd0 : 0 < d := by omega
      simp [Items.maxOver, B, Items.w1, hd0, I]
    refine ⟨rfl, Aux411.mkInitN_0 d, Aux411.mkInitN_1 d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [s₀, Aux411.mkInitState, Aux411.mkInitR]
    · simp [s₀, Aux411.mkInitState, Aux411.mkInitR]
    · rw [hmaxAP]; exact Aux411.mkInitR_zero_below_vA2 d 2 (by omega) (by omega)
    · rw [hmaxAW]; exact Aux411.mkInitR_zero_below_vA2 d 3 (by omega) (by omega)
    · rw [hmaxBP]; exact Aux411.mkInitR_zero_below_vA2 d 4 (by omega) (by omega)
    · rw [hmaxBW]; exact Aux411.mkInitR_zero_below_vA2 d 5 (by omega) (by omega)
    · intro t; have := t.isLt; exact Aux411.mkInitR_zero_below_vA2 d (6 + t.val) (by omega) (by omega)
    · rw [show s₀.N 4 = _ from Aux411.mkInitN_4 d]; omega
    · rw [show s₀.N 2 = 6 + d from Aux411.mkInitN_2 d]
      refine ⟨by simp [hlistA], fun x => ?_, fun e he => ?_⟩
      · rw [Aux411.inDom_iff_zero d hd I rfl hIw0 Wt rfl A x]
        simp [hlistA, hkeyA]
      · rw [hlistA, List.mem_singleton] at he; subst he
        have heN : s₀.N (6 + d + 4) = vA := Aux411.mkInitN_eA d
        refine Or.inr ⟨by rw [heN]; dsimp [vA]; omega, A, rfl, ?_⟩
        rw [heN]; exact hvA_vitem
    · rw [show s₀.N 2 = 6 + d from Aux411.mkInitN_2 d, show s₀.N 4 = _ from Aux411.mkInitN_4 d]
      refine ⟨by omega, by rw [show s₀.N (6 + d) = 1 from Aux411.mkInitN_tbA d]; omega, fun e he => ?_⟩
      rw [hlistA, List.mem_singleton] at he; subst he
      have heN : s₀.N (6 + d + 4) = vA := Aux411.mkInitN_eA d
      refine ⟨by omega, by omega, fun _ => ?_⟩
      rw [heN]
      refine ⟨[0], [vA], hvA_walk, fun u hu => ?_⟩
      simp only [List.mem_singleton] at hu; subst hu; dsimp [vA]; omega
    · rw [show s₀.N 3 = 6 + d + 2 from Aux411.mkInitN_3 d]
      refine ⟨by simp [hlistB], fun x => ?_, fun e he => ?_⟩
      · rw [Aux411.inDom_iff_zero d hd I rfl hIw0 Wt rfl B x]
        simp [hlistB, hkeyB]
      · rw [hlistB, List.mem_singleton] at he; subst he
        have heN : s₀.N (6 + d + 4 + (d + 1)) = vB := Aux411.mkInitN_eB d
        refine Or.inr ⟨by rw [heN]; dsimp [vB, vA]; omega, B, rfl, ?_⟩
        rw [heN]; exact hvB_vitem
    · rw [show s₀.N 3 = 6 + d + 2 from Aux411.mkInitN_3 d, show s₀.N 4 = _ from Aux411.mkInitN_4 d]
      refine ⟨by omega, by rw [show s₀.N (6 + d + 2) = 1 from Aux411.mkInitN_tbB d]; omega, fun e he => ?_⟩
      rw [hlistB, List.mem_singleton] at he; subst he
      have heN : s₀.N (6 + d + 4 + (d + 1)) = vB := Aux411.mkInitN_eB d
      refine ⟨by omega, by omega, fun _ => ?_⟩
      rw [heN]
      refine ⟨[1], [vB], hvB_walk, fun u hu => ?_⟩
      simp only [List.mem_singleton] at hu; subst hu; dsimp [vB, vA]; omega
  have hA_ne : A.Nonempty := ⟨i0, by simp [A]⟩
  have hB_ne : B.Nonempty := ⟨i1, by simp [B]⟩
  have hAB_disj : Disjoint A B := by simp [A, B, i0, i1]
  obtain ⟨t, _, ht_bound, h, hIsConv, hTabOut⟩ :=
    hAll d 2 1 hd (by norm_num) (by omega) I hI Wt (fun _ _ _ => le_rfl)
      1 1 zero_lt_one le_rfl zero_lt_one le_rfl A B hA_ne hB_ne hAB_disj f g hfA hgB s₀ hConv
  have hbound_eq : C * (Real.logb 2 (((2 : ℕ) : ℝ) / 1) / 1) ^ (C * (d : ℝ)) = C := by
    push_cast
    have hlog : Real.logb 2 ((2 : ℝ) / 1) = 1 := by
      rw [div_one]
      exact Real.logb_self_eq_one (by norm_num)
    rw [hlog, div_one, Real.one_rpow, mul_one]
  rw [hbound_eq] at ht_bound
  have ht_ceil : t ≤ Nat.ceil C :=
    Nat.cast_le.mp ((by linarith : (t : ℝ) ≤ C).trans (Nat.le_ceil C))
  let z := Aux411.zeroPVec d
  have hzAB : InDom I Wt 1 1 (A ∪ B) z :=
    (Aux411.inDom_iff_zero d hd I rfl hIw0 Wt rfl (A ∪ B) z).mpr rfl
  have hzA : InDom I Wt 1 1 A z :=
    (Aux411.inDom_iff_zero d hd I rfl hIw0 Wt rfl A z).mpr rfl
  have hzB : InDom I Wt 1 1 B z :=
    (Aux411.inDom_iff_zero d hd I rfl hIw0 Wt rfl B z).mpr rfl
  have hzDom : (z.add z).Dom z :=
    ⟨by simp [z, Aux411.zeroPVec, PVec.add], fun _ _ => by simp [z, Aux411.zeroPVec, PVec.add]⟩
  obtain ⟨_, _, Sy, Sz, _, _, _, hfy, hgz, hhz, _⟩ :=
    (hIsConv z hzAB).2 ⟨z, z, hzA, hzB, hzDom, by simp [f], by simp [g]⟩
  have hSy : Sy = A := Option.some.inj hfy.symm
  have hSz : Sz = B := Option.some.inj hgz.symm
  subst hSy hSz
  let s := run P s₀ t
  have hz_mem := (hTabOut.2.1 z).mp hzAB
  rw [List.mem_map] at hz_mem
  obtain ⟨e, he_in, he_key⟩ := hz_mem
  rcases hTabOut.2.2 e he_in with ⟨_, hnone⟩ | ⟨_, S, hsome, hvS⟩
  · rw [he_key, hhz] at hnone; cases hnone
  · rw [he_key, hhz] at hsome
    have hS_eq : S = A ∪ B := Option.some.inj hsome.symm
    subst hS_eq
    obtain ⟨⟨_, _, _, _, _, _, _, _, hw_cells⟩, _⟩ := hvS
    obtain ⟨W, hW_card, hW_mem⟩ := Aux411.run_R_eq_two_finset P s₀ (Aux411.mkInitR_no2 d) t
    let idxMap : Fin (d - 1) → ℕ := fun j => s.N e + 1 + (j.val + 1)
    have hidx_inj : Function.Injective idxMap := by
      intro j₁ j₂ hj; dsimp [idxMap] at hj; exact Fin.ext (by omega)
    let M : Finset ℕ := Finset.univ.image idxMap
    have hM_card : M.card = d - 1 := by
      rw [Finset.card_image_of_injective _ hidx_inj, Finset.card_univ, Fintype.card_fin]
    have hM_sub : M ⊆ W := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨j, _, rfl⟩ := hm
      apply hW_mem
      let tj : Fin d := ⟨j.val + 1, by have := j.isLt; omega⟩
      have hwc := hw_cells tj
      have hwt2 : I.weight (A ∪ B) tj = 2 := by
        have hAB : A ∪ B = {i0, i1} := rfl
        rw [hAB]
        simp [Items.weight, i0, i1, I, tj]
        try norm_num
      simpa [idxMap, tj, hwt2] using hwc
    have hle : d - 1 ≤ t := by
      calc d - 1 = M.card := hM_card.symm
        _ ≤ W.card := Finset.card_le_card hM_sub
        _ ≤ t := hW_card
    dsimp [d] at hle
    omega

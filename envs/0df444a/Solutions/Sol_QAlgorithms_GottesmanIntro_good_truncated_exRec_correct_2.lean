-- Prove2me | solution 2 for QAlgorithms.GottesmanIntro.good_truncated_exRec_correct
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:52:43.077325+00:00
-- url     : https://prove2.me/submissions/a6263a46-fc61-4eaa-be0e-4839c784e395
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Theorems.Thm_QAlgorithms_GottesmanIntro_exRecCorrectStar_of_exRecCorrect
set_option autoImplicit false

open scoped Matrix BigOperators
open QAlgorithms
open QAlgorithms.GottesmanIntro

noncomputable section

namespace SolGoodTruncated

def IsMatrixLinear {ι κ : Type*} (Ψ : Superop ι κ) : Prop :=
  (∀ A B : Matrix ι ι ℂ, Ψ (A + B) = Ψ A + Ψ B) ∧
  (∀ (c : ℂ) (A : Matrix ι ι ℂ), Ψ (c • A) = c • Ψ A)

private lemma IsMatrixLinear.map_zero {ι κ : Type*} {Ψ : Superop ι κ} (hΨ : IsMatrixLinear Ψ) :
    Ψ 0 = 0 := by
  have h := hΨ.2 0 0
  simpa using h

private lemma IsMatrixLinear.map_sum {α ι κ : Type*} {Ψ : Superop ι κ} (hΨ : IsMatrixLinear Ψ)
    (s : Finset α) (f : α → Matrix ι ι ℂ) :
    Ψ (∑ a ∈ s, f a) = ∑ a ∈ s, Ψ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hΨ.map_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, hΨ.1, ih, Finset.sum_insert ha]

private lemma isMatrixLinear_id {ι : Type*} : IsMatrixLinear (fun ρ : Matrix ι ι ℂ => ρ) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

private lemma isMatrixLinear_conjSuperop {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) :
    IsMatrixLinear (conjSuperop A) := by
  refine ⟨fun X Y => ?_, fun c X => ?_⟩
  · simp [conjSuperop, Matrix.mul_add, Matrix.add_mul]
  · simp [conjSuperop, Matrix.mul_smul, Matrix.smul_mul]

private lemma isMatrixLinear_filterOp (P : FTProtocol) (r : ℕ) :
    IsMatrixLinear (P.filterOp r) :=
  isMatrixLinear_conjSuperop (filterProj P.code r)

private lemma isMatrixLinear_krausApply {K ι κ : Type*} [Fintype K] [Fintype ι]
    (E : K → Matrix κ ι ℂ) :
    IsMatrixLinear (krausApply E) := by
  refine ⟨fun X Y => ?_, fun c X => ?_⟩
  · simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  · simp [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

private lemma isMatrixLinear_of_isChannel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {Φ : Superop ι κ} (hΦ : IsChannel Φ) :
    IsMatrixLinear Φ := by
  obtain ⟨m, E, _, hE⟩ := hΦ
  have hfun : Φ = krausApply E := funext hE
  rw [hfun]
  exact isMatrixLinear_krausApply E

private lemma loc_apply_add {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E] (l : Loc N)
    (O : List Bool → ℕ × ℕ → Option Bool) (e : Option (Superop (Qubits N × E) (Qubits N × E)))
    (he : ∀ Φ, e = some Φ → IsMatrixLinear Φ) (ρ₁ ρ₂ : CQState N E) :
    l.apply O e (ρ₁ + ρ₂) = l.apply O e ρ₁ + l.apply O e ρ₂ := by
  rcases l with ⟨kind, wires, cond⟩
  funext r
  cases heq : e with
  | none =>
    cases kind <;> simp only [Loc.apply, Pi.add_apply]
    · exact (isMatrixLinear_krausApply _).1 _ _
    · split_ifs
      · exact (isMatrixLinear_conjSuperop _).1 _ _
      · rfl
    · split_ifs
      · exact (isMatrixLinear_conjSuperop _).1 _ _
      · rfl
    · split_ifs
      · exact (isMatrixLinear_conjSuperop _).1 _ _
      · rfl
    · cases hlast : r.getLast? with
      | none => simp
      | some b => exact (isMatrixLinear_conjSuperop _).1 _ _
  | some Φ =>
    have hΦ := he Φ heq
    cases kind <;> simp only [Loc.apply, Pi.add_apply]
    · rw [(isMatrixLinear_krausApply _).1, hΦ.1]
    · split_ifs
      · rw [(isMatrixLinear_conjSuperop _).1, hΦ.1]
      · exact hΦ.1 _ _
    · split_ifs
      · rw [(isMatrixLinear_conjSuperop _).1, hΦ.1]
      · exact hΦ.1 _ _
    · split_ifs
      · rw [(isMatrixLinear_conjSuperop _).1, hΦ.1]
      · exact hΦ.1 _ _
    · cases hlast : r.getLast? with
      | none => simp
      | some b =>
        simp only []
        rw [hΦ.1, (isMatrixLinear_conjSuperop _).1]
    · exact hΦ.1 _ _

private lemma loc_apply_smul {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E] (l : Loc N)
    (O : List Bool → ℕ × ℕ → Option Bool) (e : Option (Superop (Qubits N × E) (Qubits N × E)))
    (he : ∀ Φ, e = some Φ → IsMatrixLinear Φ) (c : ℂ) (ρ : CQState N E) :
    l.apply O e (c • ρ) = c • l.apply O e ρ := by
  rcases l with ⟨kind, wires, cond⟩
  funext r
  cases heq : e with
  | none =>
    cases kind <;> simp only [Loc.apply, Pi.smul_apply]
    · exact (isMatrixLinear_krausApply _).2 _ _
    · split_ifs
      · exact (isMatrixLinear_conjSuperop _).2 _ _
      · rfl
    · split_ifs
      · exact (isMatrixLinear_conjSuperop _).2 _ _
      · rfl
    · split_ifs
      · exact (isMatrixLinear_conjSuperop _).2 _ _
      · rfl
    · cases hlast : r.getLast? with
      | none => simp
      | some b => exact (isMatrixLinear_conjSuperop _).2 _ _
  | some Φ =>
    have hΦ := he Φ heq
    cases kind <;> simp only [Loc.apply, Pi.smul_apply]
    · rw [(isMatrixLinear_krausApply _).2, hΦ.2]
    · split_ifs
      · rw [(isMatrixLinear_conjSuperop _).2, hΦ.2]
      · exact hΦ.2 _ _
    · split_ifs
      · rw [(isMatrixLinear_conjSuperop _).2, hΦ.2]
      · exact hΦ.2 _ _
    · split_ifs
      · rw [(isMatrixLinear_conjSuperop _).2, hΦ.2]
      · exact hΦ.2 _ _
    · cases hlast : r.getLast? with
      | none => simp
      | some b =>
        simp only []
        rw [hΦ.2, (isMatrixLinear_conjSuperop _).2]
    · exact hΦ.2 _ _

private lemma runStep_add {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (O : List Bool → ℕ × ℕ → Option Bool) (err : ErrAssign N E)
    (herr : ∀ ℓ Φ, err ℓ = some Φ → IsMatrixLinear Φ) (s : ℕ) :
    ∀ (ls : List (Loc N)) (j : ℕ) (ρ₁ ρ₂ : CQState N E),
      runStep O err s ls j (ρ₁ + ρ₂) = runStep O err s ls j ρ₁ + runStep O err s ls j ρ₂
  | [], _, _, _ => rfl
  | l :: ls, j, ρ₁, ρ₂ => by
    simp only [runStep]
    rw [loc_apply_add l O (err (s, j)) (herr (s, j)), runStep_add O err herr s ls (j + 1)]

private lemma runStep_smul {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (O : List Bool → ℕ × ℕ → Option Bool) (err : ErrAssign N E)
    (herr : ∀ ℓ Φ, err ℓ = some Φ → IsMatrixLinear Φ) (s : ℕ) :
    ∀ (ls : List (Loc N)) (j : ℕ) (c : ℂ) (ρ : CQState N E),
      runStep O err s ls j (c • ρ) = c • runStep O err s ls j ρ
  | [], _, _, _ => rfl
  | l :: ls, j, c, ρ => by
    simp only [runStep]
    rw [loc_apply_smul l O (err (s, j)) (herr (s, j)), runStep_smul O err herr s ls (j + 1)]

private lemma runFrom_add {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (C : LocCircuit N) (err : ErrAssign N E)
    (herr : ∀ ℓ Φ, err ℓ = some Φ → IsMatrixLinear Φ) :
    ∀ (steps : List (List (Loc N))) (s : ℕ) (ρ₁ ρ₂ : CQState N E),
      C.runFrom err steps s (ρ₁ + ρ₂) = C.runFrom err steps s ρ₁ + C.runFrom err steps s ρ₂
  | [], _, _, _ => rfl
  | st :: rest, s, ρ₁, ρ₂ => by
    simp only [LocCircuit.runFrom]
    rw [runStep_add _ err herr s st 0, runFrom_add C err herr rest (s + 1)]

private lemma runFrom_smul {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (C : LocCircuit N) (err : ErrAssign N E)
    (herr : ∀ ℓ Φ, err ℓ = some Φ → IsMatrixLinear Φ) :
    ∀ (steps : List (List (Loc N))) (s : ℕ) (c : ℂ) (ρ : CQState N E),
      C.runFrom err steps s (c • ρ) = c • C.runFrom err steps s ρ
  | [], _, _, _ => rfl
  | st :: rest, s, c, ρ => by
    simp only [LocCircuit.runFrom]
    rw [runStep_smul _ err herr s st 0, runFrom_smul C err herr rest (s + 1)]

private lemma pauliErr_isMatrixLinear {N : ℕ} (C : LocCircuit N) (fa : PauliArrangement) :
    ∀ ℓ Φ, pauliErr C fa ℓ = some Φ → IsMatrixLinear Φ := by
  intro ℓ Φ h
  unfold pauliErr at h
  split at h
  · injection h with hΦ
    subst hΦ
    exact isMatrixLinear_conjSuperop _
  · contradiction

private lemma gadgetOut_add {N : ℕ} (G : LocCircuit N) (fa : PauliArrangement)
    (X Y : Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ) (B : List Bool → Bool) :
    gadgetOut G fa (X + Y) B = gadgetOut G fa X B + gadgetOut G fa Y B := by
  unfold gadgetOut LocCircuit.run
  have hin : (fun r' : List Bool => if r' = [] then X + Y else 0) =
      (fun r' : List Bool => if r' = [] then X else 0) +
        (fun r' : List Bool => if r' = [] then Y else 0) := by
    ext r' p q
    by_cases hr' : r' = [] <;> simp [hr']
  rw [hin, runFrom_add G (pauliErr G fa) (pauliErr_isMatrixLinear G fa)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

private lemma gadgetOut_smul {N : ℕ} (G : LocCircuit N) (fa : PauliArrangement)
    (c : ℂ) (X : Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ) (B : List Bool → Bool) :
    gadgetOut G fa (c • X) B = c • gadgetOut G fa X B := by
  unfold gadgetOut LocCircuit.run
  have hin : (fun r' : List Bool => if r' = [] then c • X else 0) =
      c • (fun r' : List Bool => if r' = [] then X else 0) := by
    ext r' p q
    by_cases hr' : r' = [] <;> simp [hr']
  rw [hin, runFrom_smul G (pauliErr G fa) (pauliErr_isMatrixLinear G fa)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

private lemma embedVia_add {N k n A : ℕ} (L : Qubits N ≃ (Fin k → Qubits n) × (Fin k → Qubits A))
    (X Y : Matrix (Fin k → Qubits n) (Fin k → Qubits n) ℂ) :
    embedVia L (X + Y) = embedVia L X + embedVia L Y := by
  ext p p'
  simp only [embedVia, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

private lemma embedVia_smul {N k n A : ℕ} (L : Qubits N ≃ (Fin k → Qubits n) × (Fin k → Qubits A))
    (c : ℂ) (X : Matrix (Fin k → Qubits n) (Fin k → Qubits n) ℂ) :
    embedVia L (c • X) = c • embedVia L X := by
  ext p p'
  simp only [embedVia, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

private lemma traceVia_add {N k n A : ℕ} (L : Qubits N ≃ (Fin k → Qubits n) × (Fin k → Qubits A))
    (X Y : Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ) :
    traceVia L (X + Y) = traceVia L X + traceVia L Y := by
  ext x x'
  simp [traceVia, Finset.sum_add_distrib]

private lemma traceVia_smul {N k n A : ℕ} (L : Qubits N ≃ (Fin k → Qubits n) × (Fin k → Qubits A))
    (c : ℂ) (X : Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ) :
    traceVia L (c • X) = c • traceVia L X := by
  ext x x'
  simp [traceVia, Finset.mul_sum]

private lemma isMatrixLinear_ecOp (P : FTProtocol) (fa : PauliArrangement) :
    IsMatrixLinear (P.ecOp fa) := by
  refine ⟨fun X Y => ?_, fun c X => ?_⟩
  · unfold FTProtocol.ecOp
    have hsub : Matrix.submatrix (X + Y) (fun x : Fin 1 → Qubits P.n => x 0)
        (fun x : Fin 1 → Qubits P.n => x 0) =
        Matrix.submatrix X (fun x : Fin 1 → Qubits P.n => x 0) (fun x : Fin 1 → Qubits P.n => x 0) +
          Matrix.submatrix Y (fun x : Fin 1 → Qubits P.n => x 0) (fun x : Fin 1 → Qubits P.n => x 0) := rfl
    rw [hsub, embedVia_add, gadgetOut_add, traceVia_add]
    rfl
  · unfold FTProtocol.ecOp
    have hsub : Matrix.submatrix (c • X) (fun x : Fin 1 → Qubits P.n => x 0)
        (fun x : Fin 1 → Qubits P.n => x 0) =
        c • Matrix.submatrix X (fun x : Fin 1 → Qubits P.n => x 0) (fun x : Fin 1 → Qubits P.n => x 0) := rfl
    rw [hsub, embedVia_smul, gadgetOut_smul, traceVia_smul]
    rfl

private lemma matrix_eq_sum_single {β : Type*} [Fintype β] [DecidableEq β]
    (M : Matrix β β ℂ) :
    M = ∑ b : β, ∑ b' : β, M b b' • Matrix.single b b' (1 : ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single, Matrix.of_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b' _ hb'
      exact if_neg (fun h => hb' h.2)
    · intro h
      exact False.elim (h (Finset.mem_univ j))
  · intro b _ hb
    refine Finset.sum_eq_zero fun b' _ => ?_
    exact if_neg (fun h => hb h.1)
  · intro h
    exact False.elim (h (Finset.mem_univ i))

private lemma IsMatrixLinear.apply_eq_sum_single {β γ : Type*} [Fintype β] [DecidableEq β]
    {Ψ : Superop β γ} (hΨ : IsMatrixLinear Ψ) (M : Matrix β β ℂ) (z z' : γ) :
    Ψ M z z' = ∑ b : β, ∑ b' : β, M b b' * Ψ (Matrix.single b b' 1) z z' := by
  conv_lhs => rw [matrix_eq_sum_single M]
  rw [hΨ.map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hΨ.map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [hΨ.2]
  simp [Matrix.smul_apply]

private lemma piSuperop_comp {α β γ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {k : ℕ}
    (Ψ : Fin k → Superop β γ) (Φ : Fin k → Superop α β)
    (hΨ : ∀ i, IsMatrixLinear (Ψ i)) :
    piSuperop Ψ ∘ piSuperop Φ = piSuperop (fun i => Ψ i ∘ Φ i) := by
  funext X
  ext z z'
  simp only [Function.comp_apply, piSuperop, Matrix.of_apply]
  let F : (Fin k → α) → (Fin k → α) → (Fin k → β) → (Fin k → β) → ℂ :=
    fun x x' y y' =>
      X x x' * ((∏ i : Fin k, Φ i (Matrix.single (x i) (x' i) 1) (y i) (y' i)) *
        (∏ i : Fin k, Ψ i (Matrix.single (y i) (y' i) 1) (z i) (z' i)))
  have h_rhs :
      (∑ x : Fin k → α, ∑ x' : Fin k → α,
        X x x' * ∏ i : Fin k, Ψ i (Φ i (Matrix.single (x i) (x' i) 1)) (z i) (z' i)) =
      ∑ x : Fin k → α, ∑ x' : Fin k → α, ∑ y : Fin k → β, ∑ y' : Fin k → β, F x x' y y' := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    have hprod :
        (∏ i : Fin k, Ψ i (Φ i (Matrix.single (x i) (x' i) 1)) (z i) (z' i)) =
          ∑ y : Fin k → β, ∑ y' : Fin k → β,
            (∏ i : Fin k, Φ i (Matrix.single (x i) (x' i) 1) (y i) (y' i)) *
              (∏ i : Fin k, Ψ i (Matrix.single (y i) (y' i) 1) (z i) (z' i)) := by
      have hp1 :
          (∏ i : Fin k, Ψ i (Φ i (Matrix.single (x i) (x' i) 1)) (z i) (z' i)) =
            ∏ i : Fin k, ∑ y : β, ∑ y' : β,
              Φ i (Matrix.single (x i) (x' i) 1) y y' *
                Ψ i (Matrix.single y y' 1) (z i) (z' i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        exact (hΨ i).apply_eq_sum_single (Φ i (Matrix.single (x i) (x' i) 1)) (z i) (z' i)
      rw [hp1, Fintype.prod_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      exact Finset.prod_mul_distrib
    rw [hprod, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
  have h_lhs :
      (∑ y : Fin k → β, ∑ y' : Fin k → β,
        (∑ x : Fin k → α, ∑ x' : Fin k → α,
          X x x' * ∏ i : Fin k, Φ i (Matrix.single (x i) (x' i) 1) (y i) (y' i)) *
            ∏ i : Fin k, Ψ i (Matrix.single (y i) (y' i) 1) (z i) (z' i)) =
      ∑ y : Fin k → β, ∑ y' : Fin k → β, ∑ x : Fin k → α, ∑ x' : Fin k → α, F x x' y y' := by
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x' _ => ?_
    dsimp [F]
    ring
  rw [h_lhs, h_rhs]
  calc ∑ y : Fin k → β, ∑ y' : Fin k → β, ∑ x : Fin k → α, ∑ x' : Fin k → α, F x x' y y'
      = ∑ y : Fin k → β, ∑ x : Fin k → α, ∑ y' : Fin k → β, ∑ x' : Fin k → α, F x x' y y' := by
          refine Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ x : Fin k → α, ∑ y : Fin k → β, ∑ y' : Fin k → β, ∑ x' : Fin k → α, F x x' y y' :=
          Finset.sum_comm
    _ = ∑ x : Fin k → α, ∑ y : Fin k → β, ∑ x' : Fin k → α, ∑ y' : Fin k → β, F x x' y y' := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ x : Fin k → α, ∑ x' : Fin k → α, ∑ y : Fin k → β, ∑ y' : Fin k → β, F x x' y y' := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_comm

private lemma gateExRecCorrect_of_good (P : FTProtocol) (hP : P.IsFaultTolerant)
    (κ : LocKind) (hκ : κ.IsGateOrWait)
    (lead trail : Fin κ.arity → PauliArrangement) (gad : PauliArrangement)
    (trunc : Finset (Fin κ.arity))
    (hgood : ∑ i, faultCount P.ec (lead i) + faultCount (P.gadget κ) gad +
      ∑ i ∈ Finset.univ.filter (fun i => i ∉ trunc), faultCount P.ec (trail i) ≤ P.t) :
    P.GateExRecCorrect κ lead trail gad trunc := by
  rcases hP with ⟨_, _, hDec, _, _, _, _, _, _, _, hGateA, hGateB, hECA, hECB⟩
  have hLinDec : IsMatrixLinear P.dec := isMatrixLinear_of_isChannel hDec.1
  let r : Fin κ.arity → ℕ := fun i => faultCount P.ec (lead i)
  let R : ℕ := faultCount (P.gadget κ) gad + ∑ i, r i
  have hR_le : R ≤ P.t := by
    dsimp [R, r]
    omega
  have hr_le : ∀ i : Fin κ.arity, r i ≤ P.t := by
    intro i
    have hi : r i ≤ ∑ j : Fin κ.arity, r j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have htrail_le : ∀ j : Fin κ.arity, j ∉ trunc → R + faultCount P.ec (trail j) ≤ P.t := by
    intro j hj
    have hj_mem : j ∈ Finset.univ.filter (fun i : Fin κ.arity => i ∉ trunc) := by
      simp [hj]
    have hj_sum : faultCount P.ec (trail j) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin κ.arity => i ∉ trunc), faultCount P.ec (trail i) :=
      Finset.single_le_sum (f := fun i => faultCount P.ec (trail i)) (fun _ _ => Nat.zero_le _) hj_mem
    dsimp [R, r]
    omega
  have hlead_filter :
      piSuperop (fun i => P.filterOp (r i)) ∘ P.leadOp lead = P.leadOp lead := by
    unfold FTProtocol.leadOp
    rw [piSuperop_comp (fun i => P.filterOp (r i)) (fun i => P.ecOp (lead i))
      (fun i => isMatrixLinear_filterOp P (r i))]
    congr 1
    funext i
    exact hECA (lead i) (hr_le i)
  have htrail_dec :
      piSuperop (fun _ : Fin κ.arity => P.dec) ∘ P.trailOp trail trunc ∘
          piSuperop (fun _ : Fin κ.arity => P.filterOp R) =
        piSuperop (fun _ : Fin κ.arity => P.dec) ∘
          piSuperop (fun _ : Fin κ.arity => P.filterOp R) := by
    unfold FTProtocol.trailOp
    have hLinTrail : ∀ j : Fin κ.arity,
        IsMatrixLinear (if j ∈ trunc then (fun ρ => ρ) else P.ecOp (trail j)) := by
      intro j
      split_ifs
      · exact isMatrixLinear_id
      · exact isMatrixLinear_ecOp P (trail j)
    have hcomp1 :
        piSuperop (fun j : Fin κ.arity => if j ∈ trunc then (fun ρ => ρ) else P.ecOp (trail j)) ∘
            piSuperop (fun _ : Fin κ.arity => P.filterOp R) =
          piSuperop (fun j : Fin κ.arity =>
            (if j ∈ trunc then (fun ρ => ρ) else P.ecOp (trail j)) ∘ P.filterOp R) :=
      piSuperop_comp _ _ hLinTrail
    rw [hcomp1]
    rw [piSuperop_comp (fun _ : Fin κ.arity => P.dec) _ (fun _ => hLinDec)]
    rw [piSuperop_comp (fun _ : Fin κ.arity => P.dec) (fun _ : Fin κ.arity => P.filterOp R)
      (fun _ => hLinDec)]
    congr 1
    funext j
    by_cases hj : j ∈ trunc
    · simp [hj]; rfl
    · simp only [hj, ↓reduceIte]
      exact hECB (trail j) R (htrail_le j hj)
  have hGA := hGateA κ hκ gad r hR_le
  have hGB := hGateB κ hκ gad r hR_le
  have hlead_pt : ∀ X, piSuperop (fun i => P.filterOp (r i)) (P.leadOp lead X) = P.leadOp lead X :=
    fun X => congrFun hlead_filter X
  have hGA_pt : ∀ X,
      piSuperop (fun _ : Fin κ.arity => P.filterOp R)
        (P.gateOp κ gad (piSuperop (fun i => P.filterOp (r i)) X)) =
        P.gateOp κ gad (piSuperop (fun i => P.filterOp (r i)) X) :=
    fun X => congrFun hGA X
  have htrail_pt : ∀ X,
      piSuperop (fun _ : Fin κ.arity => P.dec)
        (P.trailOp trail trunc (piSuperop (fun _ : Fin κ.arity => P.filterOp R) X)) =
        piSuperop (fun _ : Fin κ.arity => P.dec)
          (piSuperop (fun _ : Fin κ.arity => P.filterOp R) X) :=
    fun X => congrFun htrail_dec X
  have hGB_pt : ∀ X,
      piSuperop (fun _ : Fin κ.arity => P.dec)
        (P.gateOp κ gad (piSuperop (fun i => P.filterOp (r i)) X)) =
        conjSuperop κ.idealMatrix
          (piSuperop (fun _ : Fin κ.arity => P.dec) (piSuperop (fun i => P.filterOp (r i)) X)) :=
    fun X => congrFun hGB X
  unfold FTProtocol.GateExRecCorrect
  funext X
  simp only [Function.comp_apply]
  calc piSuperop (fun _ => P.dec) (P.trailOp trail trunc (P.gateOp κ gad (P.leadOp lead X)))
      = piSuperop (fun _ => P.dec) (P.trailOp trail trunc
          (P.gateOp κ gad (piSuperop (fun i => P.filterOp (r i)) (P.leadOp lead X)))) := by
            rw [hlead_pt]
    _ = piSuperop (fun _ => P.dec) (P.trailOp trail trunc
          (piSuperop (fun _ => P.filterOp R)
            (P.gateOp κ gad (piSuperop (fun i => P.filterOp (r i)) (P.leadOp lead X))))) := by
            rw [hGA_pt]
    _ = piSuperop (fun _ => P.dec)
          (piSuperop (fun _ => P.filterOp R)
            (P.gateOp κ gad (piSuperop (fun i => P.filterOp (r i)) (P.leadOp lead X)))) := by
            rw [htrail_pt]
    _ = piSuperop (fun _ => P.dec)
          (P.gateOp κ gad (piSuperop (fun i => P.filterOp (r i)) (P.leadOp lead X))) := by
            rw [hGA_pt]
    _ = conjSuperop κ.idealMatrix
          (piSuperop (fun _ => P.dec) (piSuperop (fun i => P.filterOp (r i)) (P.leadOp lead X))) := by
            rw [hGB_pt]
    _ = conjSuperop κ.idealMatrix (piSuperop (fun _ => P.dec) (P.leadOp lead X)) := by
            rw [hlead_pt]

end SolGoodTruncated

theorem solution (P : FTProtocol) (hP : P.IsFaultTolerant) (κ : LocKind)
    (F : ExRecFaults κ) (trunc : Finset (Fin κ.trailCount)) (htrunc : trunc.Nonempty)
    (hgood : F.count P trunc ≤ P.t) :
    ExRecCorrect P κ F trunc ∧
      ∀ (σ : ℕ) (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ), IsStarDecoder P.dec W →
        ExRecCorrectStar P W κ F trunc := by
  have hcorr : ExRecCorrect P κ F trunc := by
    cases κ with
    | meas =>
      obtain ⟨i, _⟩ := htrunc
      exact Fin.elim0 i
    | prep =>
      obtain ⟨i, hi⟩ := htrunc
      have hi0 : i = (⟨0, by decide⟩ : Fin LocKind.prep.trailCount) :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.2))
      rw [hi0] at hi
      change P.dec ((if (⟨0, by decide⟩ : Fin LocKind.prep.trailCount) ∈ trunc then (fun ρ => ρ)
        else P.ecOp (F.trail ⟨0, by decide⟩)) (P.prepState F.gad)) = pureDensity (ket false)
      rw [if_pos hi]
      have hPrepB := hP.2.2.2.2.2.2.2.2.2.1
      apply hPrepB F.gad
      unfold ExRecFaults.count at hgood
      omega
    | had =>
      exact SolGoodTruncated.gateExRecCorrect_of_good P hP .had (Or.inl rfl)
        F.lead F.trail F.gad trunc hgood
    | tgate =>
      exact SolGoodTruncated.gateExRecCorrect_of_good P hP .tgate (Or.inr (Or.inl rfl))
        F.lead F.trail F.gad trunc hgood
    | cnot =>
      exact SolGoodTruncated.gateExRecCorrect_of_good P hP .cnot (Or.inr (Or.inr (Or.inl rfl)))
        F.lead F.trail F.gad trunc hgood
    | wait =>
      exact SolGoodTruncated.gateExRecCorrect_of_good P hP .wait (Or.inr (Or.inr (Or.inr rfl)))
        F.lead F.trail F.gad trunc hgood
  exact ⟨hcorr, fun σ W hW =>
    QAlgorithms.GottesmanIntro.exRecCorrectStar_of_exRecCorrect P hP W hW κ F trunc hcorr⟩

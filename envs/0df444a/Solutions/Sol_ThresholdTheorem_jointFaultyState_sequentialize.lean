-- Prove2me | solution 1 for ThresholdTheorem.jointFaultyState_sequentialize
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T21:58:21.586123+00:00
-- url     : https://prove2.me/submissions/6a7f356f-a652-4108-8250-c7e3fa38100e

import Mathlib
import Definitions.Def_threshold_theorem_joint_faults

open Matrix
open scoped ComplexOrder Kronecker
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option autoImplicit false
open ThresholdTheorem

private noncomputable def tvSplit {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) :
    (Q → Fin 2) ≃ ((Fin k → Fin 2) × ({q : Q // q ∉ Set.range s} → Fin 2)) := by
  classical
  apply Equiv.ofBijective (fun x => (x ∘ s, fun q => x q.1))
  constructor
  · intro x y h
    apply funext
    intro q
    by_cases hq : q ∈ Set.range s
    · obtain ⟨i, rfl⟩ := hq
      exact congrFun (congrArg Prod.fst h) i
    · exact congrFun (congrArg Prod.snd h) ⟨q, hq⟩
  · rintro ⟨a, b⟩
    refine ⟨fun q => if hq : q ∈ Set.range s then a (Classical.choose hq)
      else b ⟨q, hq⟩, ?_⟩
    apply Prod.ext
    · apply funext
      intro i
      dsimp
      rw [dif_pos ⟨i, rfl⟩]
      exact congrArg a (s.injective (Classical.choose_spec (show s i ∈ Set.range s from ⟨i, rfl⟩)))
    · ext q
      simp only [dif_neg q.2]

open Classical in
private lemma tv_lift_eq {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (A : QMat k) :
    liftOp s A = (A ⊗ₖ (1 : Matrix ({q : Q // q ∉ Set.range s} → Fin 2) _ ℂ)).submatrix
      (tvSplit s) (tvSplit s) := by
  classical
  ext x y
  change (if ∀ q, q ∉ Set.range s → x q = y q then A (x ∘ s) (y ∘ s) else 0) =
    A (x ∘ s) (y ∘ s) * (1 : Matrix _ _ ℂ) (fun q : {q : Q // q ∉ Set.range s} => x q)
      (fun q : {q : Q // q ∉ Set.range s} => y q)
  simp only [Matrix.one_apply]
  have h : (∀ q, q ∉ Set.range s → x q = y q) ↔
      (fun q : {q : Q // q ∉ Set.range s} => x q) = (fun q : {q : Q // q ∉ Set.range s} => y q) := by
    simp only [funext_iff, Subtype.forall]
  simp only [h]
  split_ifs <;> simp

private lemma tv_lift_mul {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (A B : QMat k) : liftOp s (A * B) = liftOp s A * liftOp s B := by
  classical
  simp only [tv_lift_eq]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]
  simp

private lemma tv_lift_star {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (A : QMat k) :
    liftOp s Aᴴ = (liftOp s A)ᴴ := by
  classical
  simp only [tv_lift_eq, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

private lemma tv_lift_one {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q) : liftOp s 1 = 1 := by
  classical
  simp only [tv_lift_eq, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

private lemma tv_lift_sum {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (L : List (QMat k)) :
    liftOp s L.sum = (L.map (liftOp s)).sum := by
  classical
  induction L with
  | nil => ext x y; simp [liftOp]
  | cons A L ih =>
    simp only [List.sum_cons, List.map_cons, ← ih]
    ext x y
    simp only [liftOp, Matrix.add_apply]
    split_ifs <;> simp

private lemma tv_complete_lift {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (K : List (QMat k)) (hK : (K.map fun A => Aᴴ * A).sum = 1) :
    (K.map fun A => (liftOp s A)ᴴ * liftOp s A).sum = 1 := by
  classical
  calc
    _ = liftOp s (K.map fun A => Aᴴ * A).sum := by
      simp only [tv_lift_sum, List.map_map, Function.comp_def, tv_lift_mul, tv_lift_star]
    _ = liftOp s 1 := by rw [hK]
    _ = 1 := tv_lift_one s


private lemma tv_gate_complete (g : Gate) : g.unitaryᴴ * g.unitary = 1 := by
  classical
  have hu1 : (Finset.univ : Finset (Fin 1 → Fin 2)) = {![0], ![1]} := by decide
  have hu2 : (Finset.univ : Finset (Fin 2 → Fin 2)) = {![0,0], ![0,1], ![1,0], ![1,1]} := by decide
  have hc1 (x : Fin 1 → Fin 2) : x = ![0] ∨ x = ![1] := by
    have h := Finset.mem_univ x
    simpa only [hu1, Finset.mem_insert, Finset.mem_singleton] using h
  have hc2 (x : Fin 2 → Fin 2) : x = ![0,0] ∨ x = ![0,1] ∨ x = ![1,0] ∨ x = ![1,1] := by
    have h := Finset.mem_univ x
    simpa only [hu2, Finset.mem_insert, Finset.mem_singleton] using h
  cases g with
  | H =>
    change hadamardMatᴴ * hadamardMat = 1
    have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      norm_cast
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc1 x with rfl | rfl <;> rcases hc1 y with rfl | rfl <;>
      simp [hadamardMat, hu1, Complex.conj_ofReal, ← div_pow,
        div_mul_div_comm, hs, hn] <;>
      field_simp [hn] <;> first | (simpa only [pow_two] using hs.symm) | ring
  | T =>
    change tMatᴴ * tMat = 1
    have he : starRingEnd ℂ (Complex.exp ((Real.pi : ℂ) / 4 * Complex.I)) *
        Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) = 1 := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp [map_div, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc1 x with rfl | rfl <;> rcases hc1 y with rfl | rfl <;>
      simp [tMat, hu1, he]
  | CNOT =>
    change cnotMatᴴ * cnotMat = 1
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc2 x with rfl | rfl | rfl | rfl <;>
      rcases hc2 y with rfl | rfl | rfl | rfl <;>
      simp [cnotMat, hu2]

private lemma tv_ideal_complete (o : Operation) :
    (o.idealKraus.map fun A => Aᴴ * A).sum = 1 := by
  classical
  have hu1 : (Finset.univ : Finset (Fin 1 → Fin 2)) = {![0], ![1]} := by decide
  have hc1 (x : Fin 1 → Fin 2) : x = ![0] ∨ x = ![1] := by
    have h := Finset.mem_univ x
    simpa only [hu1, Finset.mem_insert, Finset.mem_singleton] using h
  cases o with
  | gate g =>
    change g.unitaryᴴ * g.unitary + 0 = 1
    simpa using tv_gate_complete g
  | wait => simp [Operation.idealKraus]
  | prep =>
    change (resetKraus 0)ᴴ * resetKraus 0 + ((resetKraus 1)ᴴ * resetKraus 1 + 0) = 1
    simp only [add_zero]
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc1 x with rfl | rfl <;> rcases hc1 y with rfl | rfl <;>
      simp [resetKraus, hu1, Matrix.mul_apply, Matrix.conjTranspose_apply]


/-! ## Generic operator lemmas -/

open Classical in
private lemma lift_comp {X : Type*} {a k : ℕ} (ι : Fin a ↪ Fin k) (s : Fin k ↪ X) (A : QMat a) :
    liftOp s (liftOp ι A) = liftOp (ι.trans s) A := by
  ext x y
  simp only [liftOp, Function.Embedding.trans_apply]
  have hc : ((∀ q, q ∉ Set.range s → x q = y q) ∧
      (∀ i, i ∉ Set.range ι → (x ∘ s) i = (y ∘ s) i)) ↔
      (∀ q, q ∉ Set.range (ι.trans s) → x q = y q) := by
    constructor
    · rintro ⟨h1, h2⟩ q hq
      by_cases hs : q ∈ Set.range s
      · obtain ⟨i, rfl⟩ := hs
        refine h2 i ?_
        rintro ⟨j, rfl⟩
        exact hq ⟨j, rfl⟩
      · exact h1 q hs
    · intro h
      refine ⟨fun q hq => h q ?_, fun i hi => h (s i) ?_⟩
      · rintro ⟨j, rfl⟩
        exact hq ⟨ι j, rfl⟩
      · rintro ⟨j, hj⟩
        exact hi ⟨j, s.injective hj⟩
  by_cases h1 : ∀ q, q ∉ Set.range s → x q = y q
  · by_cases h2 : ∀ i, i ∉ Set.range ι → (x ∘ s) i = (y ∘ s) i
    · rw [if_pos h1, if_pos h2, if_pos (hc.1 ⟨h1, h2⟩)]
      rfl
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (hc.2 h).2)]
  · rw [if_neg h1, if_neg (fun h => h1 (hc.2 h).1)]

private lemma list_sum_flatMap {α β : Type*} [AddCommMonoid β] (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- composition of channels: first `c₁`, then `c₂`. -/
private noncomputable def chComp {k : ℕ} (c₁ c₂ : Channel k) : Channel k :=
  ⟨c₁.kraus.flatMap fun A => c₂.kraus.map fun B => B * A, by
    have h2 := c₂.trace_preserving
    have h1 := c₁.trace_preserving
    rw [List.map_flatMap]
    have : ∀ A : QMat k, ((c₂.kraus.map fun B => B * A).map fun K => Kᴴ * K).sum = Aᴴ * A := by
      intro A
      have : ((c₂.kraus.map fun B => B * A).map fun K => Kᴴ * K) =
          (c₂.kraus.map fun B => Bᴴ * B).map fun M => Aᴴ * M * A := by
        simp only [List.map_map, Function.comp_def, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [this, List.map_map]; simp only [Function.comp_def]; rw [List.sum_map_mul_right, List.sum_map_mul_left, h2, Matrix.mul_one]
    rw [list_sum_flatMap]
    simp only [this]
    exact h1⟩

private noncomputable def chId (k : ℕ) : Channel k := ⟨[1], by simp⟩

private noncomputable def chList {k : ℕ} : List (Channel k) → Channel k
  | [] => chId k
  | c :: cs => chComp c (chList cs)

private noncomputable def chLift {a k : ℕ} (ι : Fin a ↪ Fin k) (c : Channel a) : Channel k :=
  ⟨c.kraus.map (liftOp ι), by
    have := tv_complete_lift ι c.kraus c.trace_preserving
    simpa [List.map_map, Function.comp_def] using this⟩

private lemma applyKraus_add {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} (s : Fin k ↪ X)
    (K : List (QMat k)) (ρ σ : Op X) :
    applyKraus s K (ρ + σ) = applyKraus s K ρ + applyKraus s K σ := by
  induction K with
  | nil => simp [applyKraus]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Matrix.mul_add, Matrix.add_mul]
    abel

private lemma applyKraus_zero {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} (s : Fin k ↪ X)
    (K : List (QMat k)) : applyKraus s K 0 = 0 := by
  induction K with
  | nil => simp [applyKraus]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp

private lemma applyKraus_listSum {X ι : Type*} [Fintype X] [DecidableEq X] {k : ℕ} (s : Fin k ↪ X)
    (K : List (QMat k)) (l : List ι) (f : ι → Op X) :
    applyKraus s K (l.map f).sum = (l.map fun i => applyKraus s K (f i)).sum := by
  induction l with
  | nil => simp [applyKraus_zero]
  | cons a l ih => simp [applyKraus_add, ih]

private lemma applyKraus_comp {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} (s : Fin k ↪ X)
    (c₁ c₂ : Channel k) (ρ : Op X) :
    applyKraus s (chComp c₁ c₂).kraus ρ = applyKraus s c₂.kraus (applyKraus s c₁.kraus ρ) := by
  conv_rhs => rw [show applyKraus s c₁.kraus ρ =
    (c₁.kraus.map fun A => liftOp s A * ρ * (liftOp s A)ᴴ).sum from rfl, applyKraus_listSum]
  simp only [chComp, applyKraus]
  rw [List.map_flatMap, list_sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro A _
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro B _
  rw [tv_lift_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private lemma applyKraus_id {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} (s : Fin k ↪ X)
    (ρ : Op X) : applyKraus s (chId k).kraus ρ = ρ := by
  simp [chId, applyKraus, tv_lift_one]

private lemma applyKraus_list {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} (s : Fin k ↪ X)
    (cs : List (Channel k)) (ρ : Op X) :
    applyKraus s (chList cs).kraus ρ = cs.foldl (fun σ c => applyKraus s c.kraus σ) ρ := by
  induction cs generalizing ρ with
  | nil => simp [chList, applyKraus_id]
  | cons c cs ih => simp [chList, applyKraus_comp, ih]

private lemma applyKraus_lift {X : Type*} [Fintype X] [DecidableEq X] {a k : ℕ}
    (ι : Fin a ↪ Fin k) (s : Fin k ↪ X) (c : Channel a) (ρ : Op X) :
    applyKraus s (chLift ι c).kraus ρ = applyKraus (ι.trans s) c.kraus ρ := by
  simp [chLift, applyKraus, List.map_map, Function.comp_def, lift_comp]

/-- the partial isometry `|emb z⟩⟨z|`. -/
private noncomputable def Wm {X X' : Type*} [DecidableEq (X' → Fin 2)]
    (emb : (X → Fin 2) → (X' → Fin 2)) : Matrix (X' → Fin 2) (X → Fin 2) ℂ :=
  fun x' z => if x' = emb z then 1 else 0

open Classical in
private lemma lift_intertwine {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X]
    [DecidableEq X'] {k : ℕ}
    (emb : (X → Fin 2) → (X' → Fin 2)) (hemb : Function.Injective emb)
    (s : Fin k ↪ X) (s' : Fin k ↪ X')
    (h1 : ∀ z, emb z ∘ s' = z ∘ s)
    (h2 : ∀ z x', (∀ p, p ∉ Set.range s' → x' p = emb z p) →
      ∃ w, emb w = x' ∧ ∀ p, p ∉ Set.range s → w p = z p)
    (h3 : ∀ z w, (∀ p, p ∉ Set.range s → w p = z p) →
      ∀ p, p ∉ Set.range s' → emb w p = emb z p)
    (A : QMat k) : liftOp s' A * Wm emb = Wm emb * liftOp s A := by
  ext x' z
  simp only [Matrix.mul_apply, Wm]
  rw [Finset.sum_eq_single (emb z) (by intro u _ hu; simp [hu]) (by simp)]
  simp only [if_true, mul_one]
  by_cases hx : ∃ w0, x' = emb w0
  · obtain ⟨w0, rfl⟩ := hx
    rw [Finset.sum_eq_single w0 (by
      intro u _ hu; rw [if_neg (fun h => hu (hemb h).symm)]; simp) (by simp)]
    simp only [if_true, one_mul, liftOp]
    have hc : (∀ q, q ∉ Set.range s' → emb w0 q = emb z q) ↔
        (∀ q, q ∉ Set.range s → w0 q = z q) := by
      constructor
      · intro h
        obtain ⟨w, hw, hwz⟩ := h2 z (emb w0) h
        rw [hemb hw] at hwz
        exact hwz
      · exact h3 z w0
    by_cases hh : ∀ q, q ∉ Set.range s → w0 q = z q
    · rw [if_pos (hc.2 hh), if_pos hh, h1, h1]
    · rw [if_neg (fun h => hh (hc.1 h)), if_neg hh]
  · rw [Finset.sum_eq_zero (by intro w _; rw [if_neg (fun h => hx ⟨w, h⟩)]; simp)]
    simp only [liftOp]
    rw [if_neg]
    intro h
    obtain ⟨w, hw, _⟩ := h2 z x' h
    exact hx ⟨w, hw.symm⟩

private lemma applyKraus_intertwine {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X]
    [DecidableEq X'] {k a : ℕ} (W : Matrix (X' → Fin 2) (X → Fin 2) ℂ)
    (s : Fin k ↪ X) (s' : Fin a ↪ X') (K : List (QMat k))
    (f : QMat k → QMat a)
    (hW : ∀ A ∈ K, liftOp s' (f A) * W = W * liftOp s A) (ρ : Op X) :
    applyKraus s' (K.map f) (W * ρ * Wᴴ) = W * applyKraus s K ρ * Wᴴ := by
  induction K with
  | nil => simp [applyKraus]
  | cons A K ih =>
    have ih' := ih (fun B hB => hW B (List.mem_cons_of_mem _ hB))
    simp only [applyKraus, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      at ih' ⊢
    rw [ih']
    have h := hW A (List.mem_cons_self)
    have e1 : liftOp s' (f A) * (W * ρ * Wᴴ) * (liftOp s' (f A))ᴴ =
        (liftOp s' (f A) * W) * ρ * (liftOp s' (f A) * W)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e1, h, Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

open Classical in
private lemma lift_comm {X : Type*} [Fintype X] [DecidableEq X] {a b : ℕ}
    (s₁ : Fin a ↪ X) (s₂ : Fin b ↪ X) (hd : ∀ i j, s₁ i ≠ s₂ j) (A : QMat a) (B : QMat b) :
    liftOp s₁ A * liftOp s₂ B = liftOp s₂ B * liftOp s₁ A := by
  ext x z
  simp only [Matrix.mul_apply]
  set y₀ : X → Fin 2 := fun p => if p ∈ Set.range s₁ then z p else x p
  set y₁ : X → Fin 2 := fun p => if p ∈ Set.range s₂ then z p else x p
  have hr : ∀ p, p ∈ Set.range s₁ → p ∉ Set.range s₂ := by
    rintro p ⟨i, rfl⟩ ⟨j, hj⟩; exact hd i j hj.symm
  have hL : (∑ y, liftOp s₁ A x y * liftOp s₂ B y z) = liftOp s₁ A x y₀ * liftOp s₂ B y₀ z := by
    refine Finset.sum_eq_single y₀ (fun y _ hy => ?_) (by simp)
    simp only [liftOp]
    by_cases h1 : ∀ q, q ∉ Set.range s₁ → x q = y q
    · by_cases h2 : ∀ q, q ∉ Set.range s₂ → y q = z q
      · exfalso; apply hy; funext p
        by_cases hp : p ∈ Set.range s₁
        · simp only [y₀, if_pos hp]; exact h2 p (hr p hp)
        · simp only [y₀, if_neg hp]; exact (h1 p hp).symm
      · rw [if_neg h2]; simp
    · rw [if_neg h1]; simp
  have hR : (∑ y, liftOp s₂ B x y * liftOp s₁ A y z) = liftOp s₂ B x y₁ * liftOp s₁ A y₁ z := by
    refine Finset.sum_eq_single y₁ (fun y _ hy => ?_) (by simp)
    simp only [liftOp]
    by_cases h1 : ∀ q, q ∉ Set.range s₂ → x q = y q
    · by_cases h2 : ∀ q, q ∉ Set.range s₁ → y q = z q
      · exfalso; apply hy; funext p
        by_cases hp : p ∈ Set.range s₂
        · simp only [y₁, if_pos hp]
          exact h2 p (fun h => hr p h hp)
        · simp only [y₁, if_neg hp]; exact (h1 p hp).symm
      · rw [if_neg h2]; simp
    · rw [if_neg h1]; simp
  rw [hL, hR]
  simp only [liftOp, y₀, y₁]
  by_cases hxz : ∀ p, p ∉ Set.range s₁ → p ∉ Set.range s₂ → x p = z p
  · have c1 : ∀ q, q ∉ Set.range s₁ → x q = (if q ∈ Set.range s₁ then z q else x q) := by
      intro q hq; rw [if_neg hq]
    have c2 : ∀ q, q ∉ Set.range s₂ → (if q ∈ Set.range s₁ then z q else x q) = z q := by
      intro q hq; split_ifs with h
      · rfl
      · exact hxz q h hq
    have c3 : ∀ q, q ∉ Set.range s₂ → x q = (if q ∈ Set.range s₂ then z q else x q) := by
      intro q hq; rw [if_neg hq]
    have c4 : ∀ q, q ∉ Set.range s₁ → (if q ∈ Set.range s₂ then z q else x q) = z q := by
      intro q hq; split_ifs with h
      · rfl
      · exact hxz q hq h
    rw [if_pos c1, if_pos c2, if_pos c3, if_pos c4]
    have e1 : ((fun p => if p ∈ Set.range s₁ then z p else x p) ∘ s₁) = z ∘ s₁ := by
      funext i; simp
    have e2 : ((fun p => if p ∈ Set.range s₁ then z p else x p) ∘ s₂) = x ∘ s₂ := by
      funext j; simp only [Function.comp_apply]; rw [if_neg]; rintro ⟨i, hi⟩; exact hd i j hi
    have e3 : ((fun p => if p ∈ Set.range s₂ then z p else x p) ∘ s₂) = z ∘ s₂ := by
      funext i; simp
    have e4 : ((fun p => if p ∈ Set.range s₂ then z p else x p) ∘ s₁) = x ∘ s₁ := by
      funext j; simp only [Function.comp_apply]; rw [if_neg]; rintro ⟨i, hi⟩
      exact hd j i hi.symm
    rw [e1, e2, e3, e4, mul_comm]
  · push Not at hxz
    obtain ⟨p, hp1, hp2, hp⟩ := hxz
    have n1 : ¬ ∀ q, q ∉ Set.range s₂ → (if q ∈ Set.range s₁ then z q else x q) = z q := by
      intro h; have := h p hp2; rw [if_neg hp1] at this; exact hp this
    have n2 : ¬ ∀ q, q ∉ Set.range s₁ → (if q ∈ Set.range s₂ then z q else x q) = z q := by
      intro h; have := h p hp1; rw [if_neg hp2] at this; exact hp this
    rw [if_neg n1, if_neg n2]; simp

private lemma list_sum_comm {α β M : Type*} [AddCommMonoid M] (l₁ : List α) (l₂ : List β)
    (g : α → β → M) :
    (l₁.map fun a => (l₂.map fun b => g a b).sum).sum =
      (l₂.map fun b => (l₁.map fun a => g a b).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← List.sum_map_add]

private lemma applyKraus_comm {X : Type*} [Fintype X] [DecidableEq X] {a b : ℕ}
    (s₁ : Fin a ↪ X) (s₂ : Fin b ↪ X) (hd : ∀ i j, s₁ i ≠ s₂ j)
    (K₁ : List (QMat a)) (K₂ : List (QMat b)) (ρ : Op X) :
    applyKraus s₁ K₁ (applyKraus s₂ K₂ ρ) = applyKraus s₂ K₂ (applyKraus s₁ K₁ ρ) := by
  conv_lhs => rw [show applyKraus s₂ K₂ ρ =
    (K₂.map fun B => liftOp s₂ B * ρ * (liftOp s₂ B)ᴴ).sum from rfl, applyKraus_listSum]
  conv_rhs => rw [show applyKraus s₁ K₁ ρ =
    (K₁.map fun A => liftOp s₁ A * ρ * (liftOp s₁ A)ᴴ).sum from rfl, applyKraus_listSum]
  simp only [applyKraus]
  rw [list_sum_comm]
  congr 1
  apply List.map_congr_left
  intro A _
  congr 1
  apply List.map_congr_left
  intro B _
  have hc := lift_comm s₁ s₂ hd A B
  have hc' : (liftOp s₂ B)ᴴ * (liftOp s₁ A)ᴴ = (liftOp s₁ A)ᴴ * (liftOp s₂ B)ᴴ := by
    rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hc]
  calc liftOp s₁ A * (liftOp s₂ B * ρ * (liftOp s₂ B)ᴴ) * (liftOp s₁ A)ᴴ
      = (liftOp s₁ A * liftOp s₂ B) * ρ * ((liftOp s₂ B)ᴴ * (liftOp s₁ A)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = (liftOp s₂ B * liftOp s₁ A) * ρ * ((liftOp s₁ A)ᴴ * (liftOp s₂ B)ᴴ) := by rw [hc, hc']
    _ = _ := by simp only [Matrix.mul_assoc]

private lemma fold2 {α β γ : Type*} (l : List α) (n : ℕ) (f : β → α × ℕ → β)
    (g : γ → α × ℕ → γ) (I : ℕ → β → γ → Prop) (b : β) (c : γ) (h0 : I n b c)
    (hs : ∀ p (hp : p < l.length) b c, I (n + p) b c →
      I (n + p + 1) (f b (l[p], n + p)) (g c (l[p], n + p))) :
    I (n + l.length) ((l.zipIdx n).foldl f b) ((l.zipIdx n).foldl g c) := by
  induction l generalizing n b c with
  | nil => simpa using h0
  | cons a l ih =>
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons]
    have h1 : I (n + 1) (f b (a, n)) (g c (a, n)) := by
      have := hs 0 (by simp) b c (by simpa using h0)
      simpa using this
    have := ih (n + 1) (f b (a, n)) (g c (a, n)) h1 (fun p hp b c h => by
      have := hs (p + 1) (by simp; omega) b c (by rw [← Nat.add_assoc]; simpa [Nat.add_right_comm] using h)
      have e : n + (p + 1) = n + 1 + p := by omega
      simp only [List.getElem_cons_succ, e] at this
      exact this)
    rwa [show n + 1 + l.length = n + (l.length + 1) by omega] at this

private lemma fold_comm {α β : Type*} (l : List α) (f : β → α → β) (φ : β → β)
    (h : ∀ b a, φ (f b a) = f (φ b) a) (b : β) : φ (l.foldl f b) = l.foldl f (φ b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons]; rw [ih, h]

/-! ## Data-marginal lemmas -/

open Classical in
private noncomputable def Pdat {Q : Type*} {m : ℕ} (x : Q → Fin 2) : Op (Q ⊕ Fin m) :=
  fun u v => if u = v ∧ (fun q => u (Sum.inl q)) = x then 1 else 0

private lemma dataOut_trace {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (ρ : Op (Q ⊕ Fin m)) (x : Q → Fin 2) :
    dataOutDist ρ x = (Matrix.trace (Pdat x * ρ)).re := by
  classical
  have e1 : Matrix.trace (Pdat x * ρ) =
      ∑ u : Q ⊕ Fin m → Fin 2, if (fun q => u (Sum.inl q)) = x then ρ u u else 0 := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro u _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single u (by intro v _ hv; simp only [Pdat]; rw [if_neg (fun h => hv h.1.symm)]; simp)
      (by simp)]
    simp only [Pdat, true_and]
    split_ifs <;> simp
  rw [e1, Complex.re_sum]
  unfold dataOutDist
  rw [← (Equiv.sumArrowEquivProdArrow Q (Fin m) (Fin 2)).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single x]
  · apply Finset.sum_congr rfl; intro y _
    simp [Equiv.sumArrowEquivProdArrow]
  · intro a _ ha
    apply Finset.sum_eq_zero; intro y _
    rw [if_neg]
    · simp
    · simpa [Equiv.sumArrowEquivProdArrow] using ha
  · simp

private lemma Pdat_comm_env {Q : Type*} [Fintype Q] [DecidableEq Q] {m k : ℕ}
    (s : Fin k ↪ Q ⊕ Fin m) (hs : ∀ i, ∃ j, s i = Sum.inr j) (A : QMat k) (x : Q → Fin 2) :
    Pdat x * liftOp s A = liftOp s A * Pdat x := by
  classical
  ext u v
  simp only [Matrix.mul_apply, Pdat]
  rw [Finset.sum_eq_single u (by intro w _ hw; rw [if_neg (fun h => hw h.1.symm)]; simp)
    (by simp)]
  rw [Finset.sum_eq_single v (by intro w _ hw; rw [if_neg (fun h => hw h.1)]; simp) (by simp)]
  simp only [true_and]
  by_cases hL : liftOp s A u v = 0
  · simp [hL]
  · have hag : ∀ q, u (Sum.inl q) = v (Sum.inl q) := by
      intro q
      simp only [liftOp] at hL
      split_ifs at hL with h
      · apply h
        rintro ⟨i, hi⟩
        obtain ⟨j, hj⟩ := hs i
        rw [hj] at hi; cases hi
      · exact absurd rfl hL
    have : (fun q => u (Sum.inl q)) = (fun q => v (Sum.inl q)) := funext hag
    rw [this, mul_comm]

private lemma dataOut_envOnly {Q : Type*} [Fintype Q] [DecidableEq Q] {m k : ℕ}
    (s : Fin k ↪ Q ⊕ Fin m) (hs : ∀ i, ∃ j, s i = Sum.inr j) (K : List (QMat k))
    (hK : (K.map fun A => Aᴴ * A).sum = 1) (ρ : Op (Q ⊕ Fin m)) :
    dataOutDist (applyKraus s K ρ) = dataOutDist ρ := by
  funext x
  rw [dataOut_trace, dataOut_trace]
  congr 1
  have hc := tv_complete_lift s K hK
  have : Matrix.trace (Pdat x * applyKraus s K ρ) =
      Matrix.trace (Pdat x * ((K.map fun A => (liftOp s A)ᴴ * liftOp s A).sum) * ρ) := by
    clear hc hK
    induction K with
    | nil => simp [applyKraus]
    | cons A K ih =>
      simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
      rw [Matrix.mul_add, Matrix.trace_add, ih, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
      congr 1
      have hc1 := Pdat_comm_env s hs Aᴴ x
      rw [tv_lift_star] at hc1
      calc Matrix.trace (Pdat x * (liftOp s A * ρ * (liftOp s A)ᴴ))
          = Matrix.trace ((liftOp s A)ᴴ * (Pdat x * liftOp s A * ρ)) := by
            conv_rhs => rw [Matrix.trace_mul_comm]
            simp only [Matrix.mul_assoc]
        _ = Matrix.trace (((liftOp s A)ᴴ * Pdat x) * liftOp s A * ρ) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [← hc1]; simp only [Matrix.mul_assoc]
  rw [this, hc, Matrix.mul_one]

private lemma Wm_Pdat {Q : Type*} [Fintype Q] [DecidableEq Q] {m m' : ℕ}
    (emb : (Q ⊕ Fin m → Fin 2) → (Q ⊕ Fin m' → Fin 2)) (hemb : Function.Injective emb)
    (hd : ∀ z q, emb z (Sum.inl q) = z (Sum.inl q)) (x : Q → Fin 2) :
    (Wm emb)ᴴ * Pdat (m := m') x * Wm emb = Pdat x := by
  classical
  have e1 : ∀ M : Op (Q ⊕ Fin m'), (Wm emb)ᴴ * M = Matrix.of fun a v => M (emb a) v := by
    intro M; ext a v
    rw [Matrix.mul_apply, Finset.sum_eq_single (emb a)]
    · simp [Wm]
    · intro u _ hu; simp [Wm, Matrix.conjTranspose_apply, hu]
    · simp
  have e2 : ∀ M : Matrix (Q ⊕ Fin m → Fin 2) (Q ⊕ Fin m' → Fin 2) ℂ,
      M * Wm emb = Matrix.of fun a b => M a (emb b) := by
    intro M; ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (emb b)]
    · simp [Wm]
    · intro u _ hu; simp [Wm, hu]
    · simp
  rw [e1, e2]
  ext a b
  simp only [Matrix.of_apply, Pdat, hemb.eq_iff, hd]
  split_ifs <;> simp_all

private lemma dataOut_W {Q : Type*} [Fintype Q] [DecidableEq Q] {m m' : ℕ}
    (emb : (Q ⊕ Fin m → Fin 2) → (Q ⊕ Fin m' → Fin 2)) (hemb : Function.Injective emb)
    (hd : ∀ z q, emb z (Sum.inl q) = z (Sum.inl q)) (ρ : Op (Q ⊕ Fin m)) :
    dataOutDist (Wm emb * ρ * (Wm emb)ᴴ) = dataOutDist ρ := by
  funext x
  rw [dataOut_trace, dataOut_trace]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Wm_Pdat emb hemb hd]

/-! ## The stash embedding -/

section Emb
variable {Q : Type} [Fintype Q] [DecidableEq Q]

private noncomputable def eQ : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q

private noncomputable def stash (m : ℕ) (q : Q) : Q ⊕ Fin (m + Fintype.card Q) :=
  Sum.inr (Fin.natAdd m (eQ q))

private def envP (Q : Type) [Fintype Q] (m : ℕ) (i : Fin m) : Q ⊕ Fin (m + Fintype.card Q) :=
  Sum.inr (Fin.castAdd _ i)

open Classical in
private noncomputable def embT (m : ℕ) (T : Set Q) (z : Q ⊕ Fin m → Fin 2) :
    Q ⊕ Fin (m + Fintype.card Q) → Fin 2
  | Sum.inl q => if q ∈ T then 0 else z (Sum.inl q)
  | Sum.inr i => Fin.addCases (fun i => z (Sum.inr i))
      (fun j => if eQ.symm j ∈ T then z (Sum.inl (eQ.symm j)) else 0) i

variable (m : ℕ)

open Classical in
private lemma embT_inl (T : Set Q) (z : Q ⊕ Fin m → Fin 2) (q : Q) :
    embT m T z (Sum.inl q) = if q ∈ T then 0 else z (Sum.inl q) := rfl

open Classical in
private lemma embT_stash (T : Set Q) (z : Q ⊕ Fin m → Fin 2) (q : Q) :
    embT m T z (stash m q) = if q ∈ T then z (Sum.inl q) else 0 := by
  simp [embT, stash, Fin.addCases_right]

private lemma embT_env (T : Set Q) (z : Q ⊕ Fin m → Fin 2) (i : Fin m) :
    embT m T z (envP Q m i) = z (Sum.inr i) := by
  simp [embT, envP, Fin.addCases_left]

private lemma stash_inj : Function.Injective (stash (Q := Q) m) := by
  intro a b h
  simp only [stash, Sum.inr.injEq] at h
  exact eQ.injective (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))

private lemma stash_ne_inl (q q' : Q) : stash m q ≠ Sum.inl q' := by simp [stash]

private lemma stash_ne_env (q : Q) (i : Fin m) : stash m q ≠ envP Q m i := by
  simp only [stash, envP, ne_eq, Sum.inr.injEq]
  intro h
  have := congrArg Fin.val h
  simp at this; omega

private lemma envP_inj : Function.Injective (envP Q m) := by
  intro a b h
  simp only [envP, Sum.inr.injEq] at h
  exact Fin.ext (by have := congrArg Fin.val h; simpa using this)

private lemma pos_cases (p : Q ⊕ Fin (m + Fintype.card Q)) :
    (∃ q, p = Sum.inl q) ∨ (∃ q, p = stash m q) ∨ (∃ i, p = envP Q m i) := by
  rcases p with q | i
  · exact Or.inl ⟨q, rfl⟩
  · induction i using Fin.addCases with
    | left i => exact Or.inr (Or.inr ⟨i, rfl⟩)
    | right j => exact Or.inr (Or.inl ⟨eQ.symm j, by simp [stash]⟩)

private lemma fun_ext' (f g : Q ⊕ Fin (m + Fintype.card Q) → Fin 2)
    (h1 : ∀ q, f (Sum.inl q) = g (Sum.inl q)) (h2 : ∀ q, f (stash m q) = g (stash m q))
    (h3 : ∀ i, f (envP Q m i) = g (envP Q m i)) : f = g := by
  funext p
  rcases pos_cases m p with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨i, rfl⟩
  · exact h1 q
  · exact h2 q
  · exact h3 i

private lemma embT_inj (T : Set Q) : Function.Injective (embT m T) := by
  classical
  intro z w h
  funext p
  rcases p with q | i
  · by_cases hq : q ∈ T
    · have := congrFun h (stash m q)
      simpa [embT_stash, hq] using this
    · have := congrFun h (Sum.inl q)
      simpa [embT_inl, hq] using this
  · have := congrFun h (envP Q m i)
    simpa [embT_env] using this

private lemma embT_zero (T : Set Q) : embT m T 0 = 0 := by
  classical
  apply fun_ext' m
  · intro q; simp [embT_inl]
  · intro q; simp [embT_stash]
  · intro i; simp [embT_env]

private lemma fin_add_cases {k m : ℕ} (a : Fin (k + m)) :
    (∃ i, a = Fin.castAdd m i) ∨ ∃ i, a = Fin.natAdd k i :=
  Fin.addCases (motive := fun a => (∃ i, a = Fin.castAdd m i) ∨ ∃ i, a = Fin.natAdd k i)
    (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) a

/-- the joint-fault embedding moved to the stash -/
private noncomputable def stashEmbed {k : ℕ} (u : Fin k ↪ Q) :
    Fin (k + m) ↪ Q ⊕ Fin (m + Fintype.card Q) :=
  ⟨Fin.addCases (fun i => stash m (u i)) (fun i => envP Q m i), by
    intro a b h
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
      simp only [Fin.addCases_left, Fin.addCases_right] at h
    · rw [u.injective (stash_inj m h)]
    · exact absurd h (stash_ne_env m _ _)
    · exact absurd h.symm (stash_ne_env m _ _)
    · rw [envP_inj m h]⟩

private lemma stashEmbed_left {k : ℕ} (u : Fin k ↪ Q) (i : Fin k) :
    stashEmbed m u (Fin.castAdd m i) = stash m (u i) := by
  show Fin.addCases (motive := fun _ => Q ⊕ Fin (m + Fintype.card Q)) (fun i => stash m (u i))
    (fun i => envP Q m i) (Fin.castAdd m i) = _
  rw [Fin.addCases_left]

private lemma stashEmbed_right {k : ℕ} (u : Fin k ↪ Q) (i : Fin m) :
    stashEmbed m u (Fin.natAdd k i) = envP Q m i := by
  show Fin.addCases (motive := fun _ => Q ⊕ Fin (m + Fintype.card Q)) (fun i => stash m (u i))
    (fun i => envP Q m i) (Fin.natAdd k i) = _
  rw [Fin.addCases_right]

private lemma envEmbed_left {k : ℕ} (u : Fin k ↪ Q) (i : Fin k) :
    envEmbed m u (Fin.castAdd m i) = Sum.inl (u i) := by
  show Fin.addCases (motive := fun _ => Q ⊕ Fin m) (fun i => Sum.inl (u i))
    (fun j => Sum.inr j) (Fin.castAdd m i) = _
  rw [Fin.addCases_left]

private lemma envEmbed_right {k : ℕ} (u : Fin k ↪ Q) (i : Fin m) :
    envEmbed m u (Fin.natAdd k i) = Sum.inr i := by
  show Fin.addCases (motive := fun _ => Q ⊕ Fin m) (fun i => Sum.inl (u i))
    (fun j => Sum.inr j) (Fin.natAdd k i) = _
  rw [Fin.addCases_right]

private lemma mem_range_stashEmbed {k : ℕ} (u : Fin k ↪ Q) (p) :
    p ∈ Set.range (stashEmbed m u) ↔ (∃ i, p = stash m (u i)) ∨ ∃ i, p = envP Q m i := by
  constructor
  · rintro ⟨a, rfl⟩
    rcases fin_add_cases a with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ⟨i, stashEmbed_left m u i⟩
    · exact Or.inr ⟨i, stashEmbed_right m u i⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨_, stashEmbed_left m u i⟩
    · exact ⟨_, stashEmbed_right m u i⟩

private lemma mem_range_envEmbed {k : ℕ} (u : Fin k ↪ Q) (p) :
    p ∈ Set.range (envEmbed m u) ↔ (∃ i, p = Sum.inl (u i)) ∨ ∃ i, p = Sum.inr i := by
  constructor
  · rintro ⟨a, rfl⟩
    rcases fin_add_cases a with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ⟨i, envEmbed_left m u i⟩
    · exact Or.inr ⟨i, envEmbed_right m u i⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨_, envEmbed_left m u i⟩
    · exact ⟨_, envEmbed_right m u i⟩

open Classical in
/-- intertwining for an ideal operation on qubits outside the stashed set -/
private lemma lift_ideal_W (T : Set Q) {k : ℕ} (s : Fin k ↪ Q) (hT : ∀ i, s i ∉ T)
    (A : QMat k) :
    liftOp (s.trans (Function.Embedding.inl : Q ↪ Q ⊕ Fin (m + Fintype.card Q))) A *
        Wm (embT m T) =
      Wm (embT m T) * liftOp (s.trans (Function.Embedding.inl : Q ↪ Q ⊕ Fin m)) A := by
  apply lift_intertwine _ (embT_inj m T)
  · intro z; funext i
    simp [embT_inl, hT i]
  · intro z x' hx
    refine ⟨Sum.elim (fun q => if q ∈ Set.range s then x' (Sum.inl q) else z (Sum.inl q))
      (fun i => z (Sum.inr i)), ?_, ?_⟩
    · apply fun_ext' m
      · intro q
        by_cases hq : q ∈ Set.range s
        · obtain ⟨i, rfl⟩ := hq
          simp [embT_inl, hT i]
        · rw [hx (Sum.inl q) (by rintro ⟨i, hi⟩; exact hq ⟨i, by simpa using hi⟩)]
          rw [Set.mem_range] at hq
          simp [embT_inl, hq]
      · intro q
        rw [hx (stash m q) (by rintro ⟨i, hi⟩; exact stash_ne_inl m q _ (by simpa using hi.symm))]
        by_cases hq : q ∈ T
        · have : q ∉ Set.range s := by rintro ⟨i, rfl⟩; exact hT i hq
          rw [Set.mem_range] at this
          simp [embT_stash, hq, this]
        · simp [embT_stash, hq]
      · intro i
        rw [hx (envP Q m i) (by rintro ⟨j, hj⟩; simp [envP] at hj)]
        simp [embT_env]
    · intro p hp
      rcases p with q | i
      · have : q ∉ Set.range s := by rintro ⟨i, rfl⟩; exact hp ⟨i, rfl⟩
        rw [Set.mem_range] at this
        simp [this]
      · rfl
  · intro z w hw p hp
    rcases pos_cases m p with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨i, rfl⟩
    · have hq : q ∉ Set.range s := by rintro ⟨i, rfl⟩; exact hp ⟨i, rfl⟩
      have := hw (Sum.inl q) (by rintro ⟨i, hi⟩; exact hq ⟨i, by simpa using hi⟩)
      simp [embT_inl, this]
    · by_cases hq : q ∈ T
      · have hq' : q ∉ Set.range s := by rintro ⟨i, rfl⟩; exact hT i hq
        have := hw (Sum.inl q) (by rintro ⟨i, hi⟩; exact hq' ⟨i, by simpa using hi⟩)
        simp [embT_stash, hq, this]
      · simp [embT_stash, hq]
    · have := hw (Sum.inr i) (by rintro ⟨j, hj⟩; simp at hj)
      simp [embT_env, this]

open Classical in
/-- intertwining for a joint fault whose data qubits are stashed -/
private lemma lift_J_W (T : Set Q) {k : ℕ} (u : Fin k ↪ Q) (hu : ∀ i, u i ∈ T)
    (A : QMat (k + m)) :
    liftOp (stashEmbed m u) A * Wm (embT m T) = Wm (embT m T) * liftOp (envEmbed m u) A := by
  apply lift_intertwine _ (embT_inj m T)
  · intro z; funext a
    induction a using Fin.addCases with
    | left i => simp [stashEmbed_left, envEmbed_left, embT_stash, hu i]
    | right i => simp [stashEmbed_right, envEmbed_right, embT_env]
  · intro z x' hx
    refine ⟨Sum.elim (fun q => if q ∈ Set.range u then x' (stash m q) else z (Sum.inl q))
      (fun i => x' (envP Q m i)), ?_, ?_⟩
    · apply fun_ext' m
      · intro q
        rw [hx (Sum.inl q) (by
          rw [mem_range_stashEmbed]; rintro (⟨i, hi⟩ | ⟨i, hi⟩)
          · exact stash_ne_inl m _ _ hi.symm
          · simp [envP] at hi)]
        by_cases hq : q ∈ T
        · simp [embT_inl, hq]
        · have : q ∉ Set.range u := by rintro ⟨i, rfl⟩; exact hq (hu i)
          rw [Set.mem_range] at this
          simp [embT_inl, hq, this]
      · intro q
        by_cases hq : q ∈ T
        · by_cases hqu : q ∈ Set.range u
          · rw [Set.mem_range] at hqu
            simp [embT_stash, hq, hqu]
          · rw [hx (stash m q) (by
              rw [mem_range_stashEmbed]; rintro (⟨i, hi⟩ | ⟨i, hi⟩)
              · exact hqu ⟨i, (stash_inj m hi).symm⟩
              · exact stash_ne_env m _ _ hi)]
            rw [Set.mem_range] at hqu
            simp [embT_stash, hq, hqu]
        · have hqu : q ∉ Set.range u := by rintro ⟨i, rfl⟩; exact hq (hu i)
          rw [hx (stash m q) (by
            rw [mem_range_stashEmbed]; rintro (⟨i, hi⟩ | ⟨i, hi⟩)
            · exact hqu ⟨i, (stash_inj m hi).symm⟩
            · exact stash_ne_env m _ _ hi)]
          simp [embT_stash, hq]
      · intro i
        simp [embT_env]
    · intro p hp
      rcases p with q | i
      · have : q ∉ Set.range u := by
          rintro ⟨i, rfl⟩; exact hp ((mem_range_envEmbed m u _).2 (Or.inl ⟨i, rfl⟩))
        rw [Set.mem_range] at this
        simp [this]
      · exact absurd ((mem_range_envEmbed m u _).2 (Or.inr ⟨i, rfl⟩)) hp
  · intro z w hw p hp
    rcases pos_cases m p with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨i, rfl⟩
    · by_cases hq : q ∈ T
      · simp [embT_inl, hq]
      · have hqu : q ∉ Set.range u := by rintro ⟨i, rfl⟩; exact hq (hu i)
        have := hw (Sum.inl q) (by
          rw [mem_range_envEmbed]; rintro (⟨i, hi⟩ | ⟨i, hi⟩)
          · exact hqu ⟨i, (Sum.inl.inj hi).symm⟩
          · cases hi)
        simp [embT_inl, hq, this]
    · have hqu : q ∉ Set.range u := by
        rintro ⟨i, rfl⟩; exact hp ((mem_range_stashEmbed m u _).2 (Or.inl ⟨i, rfl⟩))
      have := hw (Sum.inl q) (by
        rw [mem_range_envEmbed]; rintro (⟨i, hi⟩ | ⟨i, hi⟩)
        · exact hqu ⟨i, (Sum.inl.inj hi).symm⟩
        · cases hi)
      simp [embT_stash, this]
    · exact absurd ((mem_range_stashEmbed m u _).2 (Or.inr ⟨i, rfl⟩)) hp

/-- permutation matrix -/
private noncomputable def Pm {K : ℕ} (π : Equiv.Perm (Fin K)) : QMat K :=
  Matrix.of fun x y => if x = y ∘ π then 1 else 0

private lemma Pm_unitary {K : ℕ} (π : Equiv.Perm (Fin K)) : (Pm π)ᴴ * Pm π = 1 := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (x ∘ π)]
  · simp only [Matrix.conjTranspose_apply, Pm, Matrix.of_apply, if_true, star_one, one_mul,
      Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · rw [if_neg, if_neg h]
      intro h'
      apply h; funext i
      have := congrFun h' (π.symm i)
      simpa using this
  · intro u _ hu
    simp [Pm, hu]
  · simp

private noncomputable def chPm {K : ℕ} (π : Equiv.Perm (Fin K)) : Channel K :=
  ⟨[Pm π], by simp [Pm_unitary]⟩

open Classical in
private lemma liftOp_Pm_swap {X : Type*} [DecidableEq X] {K : ℕ} (s : Fin K ↪ X) (a b : Fin K) :
    liftOp s (Pm (Equiv.swap a b)) =
      Matrix.of fun x y => if x = y ∘ Equiv.swap (s a) (s b) then 1 else 0 := by
  ext x y
  simp only [liftOp, Pm, Matrix.of_apply]
  have hsw : ∀ i, Equiv.swap (s a) (s b) (s i) = s (Equiv.swap a b i) := fun i =>
    (Function.Injective.map_swap s.injective a b i).symm
  have hfix : ∀ p, p ∉ Set.range s → Equiv.swap (s a) (s b) p = p := by
    intro p hp
    apply Equiv.swap_apply_of_ne_of_ne
    · rintro rfl; exact hp ⟨a, rfl⟩
    · rintro rfl; exact hp ⟨b, rfl⟩
  by_cases h : x = y ∘ Equiv.swap (s a) (s b)
  · rw [if_pos h]
    have c1 : ∀ q, q ∉ Set.range s → x q = y q := by
      intro q hq; rw [h]; simp [hfix q hq]
    have c2 : x ∘ s = (y ∘ s) ∘ Equiv.swap a b := by
      funext i; rw [h]; simp [hsw]
    rw [if_pos c1, if_pos c2]
  · rw [if_neg h]
    split_ifs with c1 c2
    · exfalso; apply h; funext p
      by_cases hp : p ∈ Set.range s
      · obtain ⟨i, rfl⟩ := hp
        have := congrFun c2 i
        simp only [Function.comp_apply] at this
        simp [this, hsw]
      · simp [c1 p hp, hfix p hp]
    · rfl
    · rfl

open Classical in
private lemma swap_W (T : Set Q) (q : Q) :
    ((Matrix.of (fun x y => if x = y ∘ Equiv.swap (Sum.inl q) (stash m q) then (1 : ℂ) else 0)) :
        Op (Q ⊕ Fin (m + Fintype.card Q))) * Wm (embT m T) = Wm (embT m (symmDiff T {q})) := by
  ext x z
  rw [Matrix.mul_apply, Finset.sum_eq_single (embT m T z)]
  · simp only [Matrix.of_apply, Wm, if_true, mul_one]
    congr 1
    apply propext
    apply Eq.congr_right
    apply fun_ext' m
    · intro q'
      by_cases hq : q' = q
      · subst hq
        simp [Equiv.swap_apply_left, embT_stash, embT_inl, Set.mem_symmDiff]
      · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (by simpa using hq)
          (fun h => stash_ne_inl m q q' h.symm)]
        simp [embT_inl, Set.mem_symmDiff, hq]
    · intro q'
      by_cases hq : q' = q
      · subst hq
        simp [Equiv.swap_apply_right, embT_stash, embT_inl, Set.mem_symmDiff]
      · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (stash_ne_inl m q' q)
          (fun h => hq (stash_inj m h))]
        simp [embT_stash, Set.mem_symmDiff, hq]
    · intro i
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (by simp [envP])
        (fun h => stash_ne_env m q i h.symm)]
      simp [embT_env]
  · intro u _ hu; simp [Wm, hu]
  · simp

end Emb

/-! ## Circuit facts -/

section Circ
variable {Q : Type} [Fintype Q] [DecidableEq Q]

private lemma arity_pos (o : Operation) : 0 < o.arity := by
  cases o with
  | gate g => cases g <;> decide
  | prep => decide
  | wait => decide

private lemma locAt_of_lt (C : Circuit Q) (t j : ℕ) (ht : t < C.length)
    (hj : j < C[t].locs.length) : locAt C (t, j) = some C[t].locs[j] := by
  simp [locAt, ht, hj]

private lemma locAt_none_of_ge (C : Circuit Q) (t j : ℕ) (ht : C.length ≤ t) :
    locAt C (t, j) = none := by
  simp [locAt, ht]

private lemma locAt_some (C : Circuit Q) (t j : ℕ) (l : Location Q) (h : locAt C (t, j) = some l) :
    ∃ (ht : t < C.length) (hj : j < C[t].locs.length), C[t].locs[j] = l := by
  simp only [locAt, Option.bind_eq_some_iff] at h
  obtain ⟨L, hL, hl⟩ := h
  rw [List.getElem?_eq_some_iff] at hL hl
  obtain ⟨ht, rfl⟩ := hL
  obtain ⟨hj, rfl⟩ := hl
  exact ⟨ht, hj, rfl⟩

private lemma two_le_sum (l : List ℕ) (j j' : ℕ) (hj : j < l.length) (hj' : j' < l.length)
    (hne : j ≠ j') : l[j] + l[j'] ≤ l.sum := by
  rw [← Fin.sum_univ_getElem l]
  have := Finset.sum_le_sum_of_subset (f := fun i : Fin l.length => l[i])
    (s := {⟨j, hj⟩, ⟨j', hj'⟩}) (t := Finset.univ) (Finset.subset_univ _)
  rw [Finset.sum_pair (by simp [Fin.ext_iff, hne])] at this
  exact this

private lemma layer_unique (L : Layer Q) (j j' : ℕ) (hj : j < L.locs.length)
    (hj' : j' < L.locs.length) (q : Q) (h1 : q ∈ Set.range L.locs[j].support)
    (h2 : q ∈ Set.range L.locs[j'].support) : j = j' := by
  by_contra hne
  have hp := L.partition q
  rw [List.count_flatMap] at hp
  have key : ∀ (i : ℕ) (hi : i < L.locs.length), q ∈ Set.range L.locs[i].support →
      1 ≤ ((L.locs.map (List.count q ∘ fun ℓ : Location Q => List.ofFn ℓ.support)))[i]'(by simpa using hi) := by
    intro i hi hq
    simp only [List.getElem_map, Function.comp_apply]
    apply List.count_pos_iff.2
    obtain ⟨a, ha⟩ := hq
    rw [List.mem_ofFn]
    exact ⟨a, ha⟩
  have := two_le_sum (L.locs.map (List.count q ∘ fun ℓ : Location Q => List.ofFn ℓ.support)) j j'
    (by simpa using hj) (by simpa using hj') hne
  have k1 := key j hj h1
  have k2 := key j' hj' h2
  omega

private lemma layer_cover (L : Layer Q) (q : Q) :
    ∃ (j : ℕ) (hj : j < L.locs.length), q ∈ Set.range L.locs[j].support := by
  have hp := L.partition q
  have : q ∈ L.locs.flatMap fun ℓ => List.ofFn ℓ.support := by
    apply List.count_pos_iff.1; omega
  rw [List.mem_flatMap] at this
  obtain ⟨ℓ, hℓ, hq⟩ := this
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hℓ
  rw [List.mem_ofFn] at hq
  exact ⟨j, hj, hq⟩

private lemma len_le_size (C : Circuit Q) (t : ℕ) (ht : t < C.length) :
    C[t].locs.length ≤ C.size := by
  unfold Circuit.size
  apply List.le_sum_of_mem
  exact List.mem_map.2 ⟨C[t], List.getElem_mem ht, rfl⟩

private lemma mem_bad_iff (C : Circuit Q) (B : Finset (ℕ × ℕ)) (t : ℕ) (ht : t < C.length)
    (q : Q) : q ∈ badQubits C B t ↔
      ∃ (j : ℕ) (hj : j < C[t].locs.length), (t, j) ∈ B ∧ q ∈ Set.range C[t].locs[j].support := by
  constructor
  · rintro ⟨j, l, hB, hl, hq⟩
    obtain ⟨_, hj, rfl⟩ := locAt_some C t j l hl
    exact ⟨j, hj, hB, hq⟩
  · rintro ⟨j, hj, hB, hq⟩
    exact ⟨j, _, hB, locAt_of_lt C t j ht hj, hq⟩

private lemma bad_empty_of_ge (C : Circuit Q) (B : Finset (ℕ × ℕ)) (t : ℕ) (ht : C.length ≤ t)
    (q : Q) : q ∉ badQubits C B t := by
  rintro ⟨j, l, _, hl, _⟩
  rw [locAt_none_of_ge C t j ht] at hl
  cases hl

private lemma not_bad_of_notin (C : Circuit Q) (B : Finset (ℕ × ℕ)) (t : ℕ) (ht : t < C.length)
    (j : ℕ) (hj : j < C[t].locs.length) (hB : (t, j) ∉ B) (i : Fin C[t].locs[j].op.arity) :
    C[t].locs[j].support i ∉ badQubits C B t := by
  rw [mem_bad_iff C B t ht]
  rintro ⟨j', hj', hB', hq⟩
  have := layer_unique C[t] j j' hj hj' _ ⟨i, rfl⟩ hq
  subst this
  exact hB hB'

private lemma bad_of_mem (C : Circuit Q) (B : Finset (ℕ × ℕ)) (t : ℕ) (ht : t < C.length)
    (j : ℕ) (hj : j < C[t].locs.length) (hB : (t, j) ∈ B) (i : Fin C[t].locs[j].op.arity) :
    C[t].locs[j].support i ∈ badQubits C B t :=
  (mem_bad_iff C B t ht _).2 ⟨j, hj, hB, ⟨i, rfl⟩⟩

private lemma pred_of_bad (C : Circuit Q) (B : Finset (ℕ × ℕ)) (t : ℕ) (ht : t < C.length)
    (j : ℕ) (hj : j < C[t].locs.length) (i : Fin C[t].locs[j].op.arity)
    (hq : C[t].locs[j].support i ∈ badQubits C B (t + 1)) : (t, j) ∈ predLocs C B := by
  classical
  obtain ⟨j', l', hB', hl', ⟨i', hi'⟩⟩ := hq
  unfold predLocs
  rw [Finset.mem_biUnion]
  refine ⟨(t + 1, j'), hB', ?_⟩
  rw [Finset.mem_image]
  refine ⟨j, ?_, by simp⟩
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨lt_of_lt_of_le hj (len_le_size C t ht), by simp, C[t].locs[j], l', ?_, hl', i, i', ?_⟩
  · simpa using locAt_of_lt C t j ht hj
  · exact hi'.symm

private lemma bad_nonempty_iff (C : Circuit Q) (B : Finset (ℕ × ℕ)) (t : ℕ) (ht : t < C.length) :
    (badQubits C B t).Nonempty ↔ ∃ j < C[t].locs.length, (t, j) ∈ B := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨j, hj, hB, _⟩ := (mem_bad_iff C B t ht q).1 hq
    exact ⟨j, hj, hB⟩
  · rintro ⟨j, hj, hB⟩
    exact ⟨_, bad_of_mem C B t ht j hj hB ⟨0, arity_pos _⟩⟩

end Circ

/-! ## Location-register channels -/

section Reg
variable {Q : Type} [Fintype Q] [DecidableEq Q] (m : ℕ)

private noncomputable def iotaJ {k k' : ℕ} (u : Fin k' ↪ Q) :
    Fin (k' + m) ↪ Fin (k + (m + Fintype.card Q)) :=
  ⟨Fin.addCases (fun i => Fin.natAdd k (Fin.natAdd m (eQ (u i))))
    (fun i => Fin.natAdd k (Fin.castAdd _ i)), by
    intro a b h
    rcases fin_add_cases a with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases fin_add_cases b with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
      simp only [Fin.addCases_left, Fin.addCases_right] at h
    · have := congrArg Fin.val h
      simp at this
      rw [u.injective (eQ.injective (Fin.ext this))]
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this
      rw [Fin.ext this]⟩

private lemma iotaJ_trans {k k' : ℕ} (s : Fin k ↪ Q) (u : Fin k' ↪ Q) :
    (iotaJ m (k := k) u).trans (envEmbed (m + Fintype.card Q) s) = stashEmbed m u := by
  ext a
  rcases fin_add_cases a with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [stashEmbed_left, Function.Embedding.trans_apply]
    show envEmbed (m + Fintype.card Q) s (Fin.addCases (motive := fun _ => Fin (k + (m + Fintype.card Q)))
      (fun i => Fin.natAdd k (Fin.natAdd m (eQ (u i))))
      (fun i => Fin.natAdd k (Fin.castAdd _ i)) (Fin.castAdd m a)) = _
    rw [Fin.addCases_left, envEmbed_right]; rfl
  · rw [stashEmbed_right, Function.Embedding.trans_apply]
    show envEmbed (m + Fintype.card Q) s (Fin.addCases (motive := fun _ => Fin (k + (m + Fintype.card Q)))
      (fun i => Fin.natAdd k (Fin.natAdd m (eQ (u i))))
      (fun i => Fin.natAdd k (Fin.castAdd _ i)) (Fin.natAdd k' a)) = _
    rw [Fin.addCases_right, envEmbed_right]; rfl

private lemma castAdd_trans {k : ℕ} (s : Fin k ↪ Q) :
    (Fin.castAddEmb (m + Fintype.card Q)).trans (envEmbed (m + Fintype.card Q) s) =
      s.trans Function.Embedding.inl := by
  ext i
  simp only [Function.Embedding.trans_apply]
  show envEmbed (m + Fintype.card Q) s (Fin.castAdd _ i) = _
  rw [envEmbed_left]; rfl

private noncomputable def swapCh {k : ℕ} (s : Fin k ↪ Q) (i : Fin k) :
    Channel (k + (m + Fintype.card Q)) :=
  chPm (Equiv.swap (Fin.castAdd _ i) (Fin.natAdd k (Fin.natAdd m (eQ (s i)))))

open Classical in
private lemma swapCh_W {k : ℕ} (s : Fin k ↪ Q) (i : Fin k) (T : Set Q) (ρ : Op (Q ⊕ Fin m)) :
    applyKraus (envEmbed (m + Fintype.card Q) s) (swapCh m s i).kraus
        (Wm (embT m T) * ρ * (Wm (embT m T))ᴴ) =
      Wm (embT m (symmDiff T {s i})) * ρ * (Wm (embT m (symmDiff T {s i})))ᴴ := by
  simp only [swapCh, chPm, applyKraus, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [liftOp_Pm_swap]
  have e1 : envEmbed (m + Fintype.card Q) s (Fin.castAdd _ i) = Sum.inl (s i) := envEmbed_left _ s i
  have e2 : envEmbed (m + Fintype.card Q) s (Fin.natAdd k (Fin.natAdd m (eQ (s i)))) =
      stash m (s i) := by rw [envEmbed_right]; rfl
  rw [e1, e2]
  have h := swap_W m T (s i)
  have key : ∀ P : Op (Q ⊕ Fin (m + Fintype.card Q)),
      P * Wm (embT m T) = Wm (embT m (symmDiff T {s i})) →
      P * (Wm (embT m T) * ρ * (Wm (embT m T))ᴴ) * Pᴴ =
        Wm (embT m (symmDiff T {s i})) * ρ * (Wm (embT m (symmDiff T {s i})))ᴴ := by
    intro P hP
    rw [show P * (Wm (embT m T) * ρ * (Wm (embT m T))ᴴ) * Pᴴ =
      (P * Wm (embT m T)) * ρ * (P * Wm (embT m T))ᴴ by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc], hP]
  apply key
  convert h using 4
  funext y
  split_ifs <;> simp_all

open Classical in
private lemma swaps_W {k : ℕ} (s : Fin k ↪ Q) (fl : List (Fin k)) (hnd : fl.Nodup)
    (T : Set Q) (ρ : Op (Q ⊕ Fin m)) :
    ∃ T' : Set Q, (∀ q, q ∈ T' ↔ (q ∈ T ↔ q ∉ fl.map s)) ∧
      applyKraus (envEmbed (m + Fintype.card Q) s) (chList (fl.map (swapCh m s))).kraus
        (Wm (embT m T) * ρ * (Wm (embT m T))ᴴ) =
      Wm (embT m T') * ρ * (Wm (embT m T'))ᴴ := by
  induction fl generalizing T with
  | nil => exact ⟨T, by simp, by simp [chList, applyKraus_id]⟩
  | cons i fl ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨T', hT', heq⟩ := ih hnd.2 (symmDiff T {s i})
    refine ⟨T', ?_, ?_⟩
    · intro q
      rw [hT', Set.mem_symmDiff]
      have hni : s i ∉ fl.map s := by
        intro h; obtain ⟨j, hj, hji⟩ := List.mem_map.1 h
        exact hnd.1 (s.injective hji ▸ hj)
      simp only [List.map_cons, List.mem_cons, Set.mem_singleton_iff]
      by_cases hq : q = s i
      · subst hq; tauto
      · tauto
    · simp only [List.map_cons, chList, applyKraus_comp, swapCh_W]
      exact heq

open Classical in
private lemma ideal_W {k : ℕ} (s : Fin k ↪ Q) (K : List (QMat k)) (T : Set Q)
    (hT : ∀ i, s i ∉ T) (ρ : Op (Q ⊕ Fin m)) :
    applyKraus (s.trans (Function.Embedding.inl : Q ↪ Q ⊕ Fin (m + Fintype.card Q))) K
        (Wm (embT m T) * ρ * (Wm (embT m T))ᴴ) =
      Wm (embT m T) * applyKraus (s.trans Function.Embedding.inl) K ρ * (Wm (embT m T))ᴴ := by
  have := applyKraus_intertwine (Wm (embT m T)) (s.trans Function.Embedding.inl)
    (s.trans (Function.Embedding.inl : Q ↪ Q ⊕ Fin (m + Fintype.card Q))) K id
    (fun A _ => lift_ideal_W m T s hT A) ρ
  simpa using this

open Classical in
private lemma J_W {k : ℕ} (s : Fin k ↪ Q) (F : JointFault Q m) (T : Set Q)
    (hT : ∀ i, F.supp i ∈ T) (ρ : Op (Q ⊕ Fin m)) :
    applyKraus (envEmbed (m + Fintype.card Q) s) (chLift (iotaJ m F.supp) F.chan).kraus
        (Wm (embT m T) * ρ * (Wm (embT m T))ᴴ) =
      Wm (embT m T) * applyKraus (envEmbed m F.supp) F.chan.kraus ρ * (Wm (embT m T))ᴴ := by
  rw [applyKraus_lift, iotaJ_trans]
  have := applyKraus_intertwine (Wm (embT m T)) (envEmbed m F.supp) (stashEmbed m F.supp)
    F.chan.kraus id (fun A _ => lift_J_W m T F.supp hT A) ρ
  simpa using this

end Reg

/-! ## The construction -/

section Main
variable {Q : Type} [Fintype Q] [DecidableEq Q] (C : Circuit Q) (m : ℕ)
  (B : Finset (ℕ × ℕ)) (J : ℕ → JointFault Q m)

open Classical in
private noncomputable def pend : ℕ → List ℕ
  | 0 => []
  | t + 1 => if (badQubits C B t).Nonempty then [] else pend t ++ [t]

private lemma pend_empty (t t' : ℕ) (h : t' ∈ pend C B t) : ¬ (badQubits C B t').Nonempty := by
  induction t with
  | zero => simp [pend] at h
  | succ t ih =>
    simp only [pend] at h
    split_ifs at h with hb
    · simp at h
    · rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact ih h
      · exact hb

private noncomputable def applyJ (F : JointFault Q m) (ρ : Op (Q ⊕ Fin m)) : Op (Q ⊕ Fin m) :=
  applyKraus (envEmbed m F.supp) F.chan.kraus ρ

private noncomputable def pendX (ts : List ℕ) (ρ : Op (Q ⊕ Fin m)) : Op (Q ⊕ Fin m) :=
  ts.foldl (fun σ t' => applyJ m (J t') σ) ρ

open Classical in
private noncomputable def flags (t j : ℕ) (l : Location Q) : List (Fin l.op.arity) :=
  (List.finRange l.op.arity).filter fun i =>
    decide (if (t, j) ∈ B then l.support i ∉ badQubits C B (t + 1)
      else l.support i ∈ badQubits C B (t + 1))

open Classical in
private noncomputable def designCh (t j : ℕ) (l : Location Q) :
    Channel (l.op.arity + (m + Fintype.card Q)) :=
  chComp
    (if (t, j) ∈ B then
      (if ∀ j' < j, (t, j') ∉ B then
        chList ((pend C B t ++ [t]).map fun t' => chLift (iotaJ m (J t').supp) (J t').chan)
       else chId _)
     else chLift (Fin.castAddEmb _) ⟨l.op.idealKraus, tv_ideal_complete l.op⟩)
    (chList ((flags C B t j l).map (swapCh m l.support)))

open Classical in
private noncomputable def faultD (t j k : ℕ) : Channel (k + (m + Fintype.card Q)) :=
  match locAt C (t, j) with
  | some l => if h : l.op.arity = k then h ▸ designCh C m B J t j l else chId _
  | none => chId _

private lemma faultD_eq (t j : ℕ) (l : Location Q) (h : locAt C (t, j) = some l) :
    faultD C m B J t j l.op.arity = designCh C m B J t j l := by
  simp [faultD, h]

/-- the stashed state -/
private noncomputable def Vc (T : Set Q) (ρ : Op (Q ⊕ Fin m)) :
    Op (Q ⊕ Fin (m + Fintype.card Q)) :=
  Wm (embT m T) * ρ * (Wm (embT m T))ᴴ

variable (hJ : ∀ t i, (J t).supp i ∈ badQubits C B t)
include hJ

private lemma pend_vac (t t' : ℕ) (h : t' ∈ pend C B t) (i : Fin (J t').k) : False :=
  pend_empty C B t t' h ⟨_, hJ t' i⟩

private lemma pend_env (t t' : ℕ) (h : t' ∈ pend C B t) (i : Fin ((J t').k + m)) :
    ∃ j, envEmbed m (J t').supp i = Sum.inr j := by
  rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact (pend_vac C m B J hJ t t' h a).elim
  · exact ⟨a, envEmbed_right m _ a⟩

private lemma dataOut_pendX (t : ℕ) (ts : List ℕ) (hts : ∀ t' ∈ ts, t' ∈ pend C B t)
    (ρ : Op (Q ⊕ Fin m)) : dataOutDist (pendX m J ts ρ) = dataOutDist ρ := by
  induction ts generalizing ρ with
  | nil => rfl
  | cons t' ts ih =>
    simp only [pendX, List.foldl_cons] at ih ⊢
    rw [ih (fun t'' h => hts t'' (List.mem_cons_of_mem _ h))]
    exact dataOut_envOnly _ (pend_env C m B J hJ t t' (hts t' List.mem_cons_self)) _
      (J t').chan.trace_preserving ρ

private lemma comm_ideal_J {k : ℕ} (s : Fin k ↪ Q) (K : List (QMat k)) (F : JointFault Q m)
    (hd : ∀ i j, s i ≠ F.supp j) (ρ : Op (Q ⊕ Fin m)) :
    applyKraus (s.trans Function.Embedding.inl) K (applyJ m F ρ) =
      applyJ m F (applyKraus (s.trans Function.Embedding.inl) K ρ) := by
  unfold applyJ
  apply applyKraus_comm
  intro i x
  rcases fin_add_cases x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [envEmbed_left]; simp [hd i a]
  · rw [envEmbed_right]; simp

private lemma comm_ideal_pend {k : ℕ} (s : Fin k ↪ Q) (K : List (QMat k)) (t : ℕ)
    (ts : List ℕ) (hts : ∀ t' ∈ ts, t' ∈ pend C B t) (ρ : Op (Q ⊕ Fin m)) :
    applyKraus (s.trans Function.Embedding.inl) K (pendX m J ts ρ) =
      pendX m J ts (applyKraus (s.trans Function.Embedding.inl) K ρ) := by
  induction ts generalizing ρ with
  | nil => rfl
  | cons t' ts ih =>
    simp only [pendX, List.foldl_cons] at ih ⊢
    rw [ih (fun t'' h => hts t'' (List.mem_cons_of_mem _ h))]
    rw [comm_ideal_J C m B J hJ s K (J t')
      (fun i j => (pend_vac C m B J hJ t t' (hts t' List.mem_cons_self) j).elim)]

private lemma pend_W (t : ℕ) {k : ℕ} (s : Fin k ↪ Q) (ts : List ℕ) (T : Set Q)
    (hts : ∀ t' ∈ ts, ∀ i, (J t').supp i ∈ T) (ρ : Op (Q ⊕ Fin m)) :
    applyKraus (envEmbed (m + Fintype.card Q) s)
        (chList (ts.map fun t' => chLift (iotaJ m (J t').supp) (J t').chan)).kraus
        (Vc m T ρ) = Vc m T (pendX m J ts ρ) := by
  induction ts generalizing ρ with
  | nil => simp [chList, applyKraus_id, pendX]
  | cons t' ts ih =>
    simp only [List.map_cons, chList, applyKraus_comp, pendX, List.foldl_cons]
    unfold Vc
    rw [J_W m s (J t') T (hts t' List.mem_cons_self)]
    exact ih (fun t'' h => hts t'' (List.mem_cons_of_mem _ h)) _

end Main

section Main2
variable {Q : Type} [Fintype Q] [DecidableEq Q] (C : Circuit Q) (m : ℕ)
  (B : Finset (ℕ × ℕ)) (J : ℕ → JointFault Q m)
  (hJ : ∀ t i, (J t).supp i ∈ badQubits C B t)
include hJ

/-- the step functions of the two layer folds -/
private noncomputable def fJ (t : ℕ) (σ : Op (Q ⊕ Fin m)) (ℓj : Location Q × ℕ) :
    Op (Q ⊕ Fin m) :=
  if (t, ℓj.2) ∈ B then σ else
    applyKraus (ℓj.1.support.trans Function.Embedding.inl) ℓj.1.op.idealKraus σ

private noncomputable def fS (t : ℕ) (σ : Op (Q ⊕ Fin (m + Fintype.card Q)))
    (ℓj : Location Q × ℕ) : Op (Q ⊕ Fin (m + Fintype.card Q)) :=
  if (t, ℓj.2) ∈ B ∪ predLocs C B then
    applyKraus (envEmbed (m + Fintype.card Q) ℓj.1.support)
      (faultD C m B J t ℓj.2 ℓj.1.op.arity).kraus σ
  else applyKraus (ℓj.1.support.trans Function.Embedding.inl) ℓj.1.op.idealKraus σ

omit hJ in
private lemma flags_mem (t j : ℕ) (l : Location Q) (i : Fin l.op.arity) :
    i ∈ flags C B t j l ↔ (if (t, j) ∈ B then l.support i ∉ badQubits C B (t + 1)
      else l.support i ∈ badQubits C B (t + 1)) := by
  classical
  simp only [flags, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

omit hJ in
private lemma flags_nodup (t j : ℕ) (l : Location Q) : (flags C B t j l).Nodup :=
  (List.nodup_finRange _).filter _

omit hJ in
private lemma Sq_unique (t : ℕ) (ht : t < C.length) (j₁ j₂ : ℕ) (h₁ : j₁ < C[t].locs.length)
    (h₂ : j₂ < C[t].locs.length) (q : Q)
    (hq₁ : q ∈ (flags C B t j₁ C[t].locs[j₁]).map C[t].locs[j₁].support)
    (hq₂ : q ∈ (flags C B t j₂ C[t].locs[j₂]).map C[t].locs[j₂].support) : j₁ = j₂ := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hq₁
  obtain ⟨b, _, hb⟩ := List.mem_map.1 hq₂
  exact layer_unique C[t] j₁ j₂ h₁ h₂ _ ⟨a, rfl⟩ ⟨b, hb⟩

private lemma inner_step (t : ℕ) (ht : t < C.length) (p : ℕ) (hp : p < C[t].locs.length)
    (σ : Op (Q ⊕ Fin m)) (T' : Set Q)
    (hT' : ∀ q, q ∈ T' ↔ (q ∈ badQubits C B t ↔ ¬ ∃ (j : ℕ) (hj : j < C[t].locs.length),
      j < p ∧ q ∈ (flags C B t j C[t].locs[j]).map C[t].locs[j].support)) :
    ∃ T'' : Set Q, (∀ q, q ∈ T'' ↔ (q ∈ badQubits C B t ↔ ¬ ∃ (j : ℕ)
        (hj : j < C[t].locs.length),
        j < p + 1 ∧ q ∈ (flags C B t j C[t].locs[j]).map C[t].locs[j].support)) ∧
      fS C m B J t (Vc m T' (if ∃ j < p, (t, j) ∈ B then
          applyJ m (J t) (pendX m J (pend C B t) σ) else σ)) (C[t].locs[p], p) =
        Vc m T'' (if ∃ j < p + 1, (t, j) ∈ B then
          applyJ m (J t) (pendX m J (pend C B t) (fJ m B t σ (C[t].locs[p], p)))
          else fJ m B t σ (C[t].locs[p], p)) := by
  classical
  set l := C[t].locs[p] with hl
  have hloc : locAt C (t, p) = some l := locAt_of_lt C t p ht hp
  have hfault := faultD_eq C m B J t p l hloc
  -- qubits of `l` are not flagged by earlier locations
  have hdisj : ∀ i (j : ℕ) (hj : j < C[t].locs.length), j < p →
      l.support i ∉ (flags C B t j C[t].locs[j]).map C[t].locs[j].support := by
    intro i j hj hjp hmem
    obtain ⟨a, _, ha⟩ := List.mem_map.1 hmem
    have := layer_unique C[t] j p hj hp (l.support i) ⟨a, ha⟩ ⟨i, rfl⟩
    omega
  have hupd : ∀ T'' : Set Q, (∀ q, q ∈ T'' ↔ (q ∈ T' ↔ q ∉ (flags C B t p l).map l.support)) →
      ∀ q, q ∈ T'' ↔ (q ∈ badQubits C B t ↔ ¬ ∃ (j : ℕ) (hj : j < C[t].locs.length),
        j < p + 1 ∧ q ∈ (flags C B t j C[t].locs[j]).map C[t].locs[j].support) := by
    intro T'' hT'' q
    rw [hT'', hT']
    have hiff : (∃ (j : ℕ) (hj : j < C[t].locs.length), j < p + 1 ∧
        q ∈ (flags C B t j C[t].locs[j]).map C[t].locs[j].support) ↔
        (∃ (j : ℕ) (hj : j < C[t].locs.length), j < p ∧
          q ∈ (flags C B t j C[t].locs[j]).map C[t].locs[j].support) ∨
        q ∈ (flags C B t p l).map l.support := by
      constructor
      · rintro ⟨j, hj, hjp, hq⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hjp with h | rfl
        · exact Or.inl ⟨j, hj, h, hq⟩
        · exact Or.inr hq
      · rintro (⟨j, hj, hjp, hq⟩ | hq)
        · exact ⟨j, hj, by omega, hq⟩
        · exact ⟨p, hp, by omega, hq⟩
    have hex : q ∈ (flags C B t p l).map l.support → ¬ ∃ (j : ℕ) (hj : j < C[t].locs.length),
        j < p ∧ q ∈ (flags C B t j C[t].locs[j]).map C[t].locs[j].support := by
      rintro hq ⟨j, hj, hjp, hq'⟩
      have := Sq_unique C B t ht j p hj hp q hq' hq
      omega
    rw [hiff]
    revert hex
    generalize (∃ (j : ℕ) (hj : j < C[t].locs.length), j < p ∧
      q ∈ (flags C B t j C[t].locs[j]).map C[t].locs[j].support) = A
    generalize (q ∈ (flags C B t p l).map l.support) = S
    generalize (q ∈ badQubits C B t) = Bq
    tauto
  by_cases hB : (t, p) ∈ B
  · -- a bad location
    have hfJ : fJ m B t σ (l, p) = σ := by
      unfold fJ; dsimp only; rw [if_pos hB]
    have hex1 : ∃ j < p + 1, (t, j) ∈ B := ⟨p, by omega, hB⟩
    rw [hfJ, if_pos hex1]
    have hΦ : (t, p) ∈ B ∪ predLocs C B := Finset.mem_union_left _ hB
    unfold fS; dsimp only; rw [if_pos hΦ]
    rw [hfault]
    unfold designCh
    rw [if_pos hB, applyKraus_comp]
    have hpre : applyKraus (envEmbed (m + Fintype.card Q) l.support)
        (if ∀ j' < p, (t, j') ∉ B then
          chList ((pend C B t ++ [t]).map fun t' => chLift (iotaJ m (J t').supp) (J t').chan)
         else chId _).kraus
        (Vc m T' (if ∃ j < p, (t, j) ∈ B then
          applyJ m (J t) (pendX m J (pend C B t) σ) else σ)) =
        Vc m T' (applyJ m (J t) (pendX m J (pend C B t) σ)) := by
      by_cases hfirst : ∀ j' < p, (t, j') ∉ B
      · have hne : ¬ ∃ j < p, (t, j) ∈ B := by
          rintro ⟨j, hj, hjB⟩; exact hfirst j hj hjB
        rw [if_pos hfirst, if_neg hne, pend_W C m B J hJ t l.support _ T']
        · simp [pendX, List.foldl_append]
        · intro t' ht' i
          rcases List.mem_append.1 ht' with h | h
          · exact (pend_vac C m B J hJ t t' h i).elim
          · rw [List.mem_singleton] at h
            subst h
            rw [hT']
            have hb := hJ t' i
            simp only [hb, true_iff]
            rintro ⟨j, hj, hjp, hq⟩
            obtain ⟨a, _, ha⟩ := List.mem_map.1 hq
            exact not_bad_of_notin C B t' ht j hj (hfirst j hjp) a (ha ▸ hb)
      · have hex : ∃ j < p, (t, j) ∈ B := by
          push Not at hfirst
          obtain ⟨j, hj, hjB⟩ := hfirst
          exact ⟨j, hj, hjB⟩
        rw [if_neg hfirst, if_pos hex, applyKraus_id]
    rw [hpre]
    obtain ⟨T'', hT'', heq⟩ := swaps_W m l.support (flags C B t p l) (flags_nodup C B t p l) T'
      (applyJ m (J t) (pendX m J (pend C B t) σ))
    exact ⟨T'', hupd T'' hT'', heq⟩
  · -- a good location
    have hfJ : fJ m B t σ (l, p) =
        applyKraus (l.support.trans Function.Embedding.inl) l.op.idealKraus σ := by
      unfold fJ; dsimp only; rw [if_neg hB]
    rw [hfJ]
    have hex_iff : (∃ j < p + 1, (t, j) ∈ B) ↔ (∃ j < p, (t, j) ∈ B) := by
      constructor
      · rintro ⟨j, hj, hjB⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
        · exact ⟨j, h, hjB⟩
        · exact absurd hjB hB
      · rintro ⟨j, hj, hjB⟩; exact ⟨j, by omega, hjB⟩
    have hnb : ∀ i, l.support i ∉ badQubits C B t := not_bad_of_notin C B t ht p hp hB
    have hnotT : ∀ i, l.support i ∉ T' := by
      intro i hi
      rw [hT'] at hi
      exact hnb i (hi.2 (fun ⟨j, hj, hjp, hq⟩ => hdisj i j hj hjp hq))
    have hcomm : applyKraus (l.support.trans Function.Embedding.inl) l.op.idealKraus
        (applyJ m (J t) (pendX m J (pend C B t) σ)) =
        applyJ m (J t) (pendX m J (pend C B t)
          (applyKraus (l.support.trans Function.Embedding.inl) l.op.idealKraus σ)) := by
      rw [comm_ideal_J C m B J hJ l.support _ (J t)
        (fun i j h => hnb i (h ▸ hJ t j))]
      rw [comm_ideal_pend C m B J hJ l.support _ t (pend C B t) (fun _ h => h)]
    have hX : applyKraus (l.support.trans Function.Embedding.inl) l.op.idealKraus
        (if ∃ j < p, (t, j) ∈ B then applyJ m (J t) (pendX m J (pend C B t) σ) else σ) =
        (if ∃ j < p + 1, (t, j) ∈ B then applyJ m (J t) (pendX m J (pend C B t)
          (applyKraus (l.support.trans Function.Embedding.inl) l.op.idealKraus σ)) else
          applyKraus (l.support.trans Function.Embedding.inl) l.op.idealKraus σ) := by
      by_cases h : ∃ j < p, (t, j) ∈ B
      · rw [if_pos h, if_pos (hex_iff.2 h), hcomm]
      · rw [if_neg h, if_neg (fun h' => h (hex_iff.1 h'))]
    by_cases hP : (t, p) ∈ predLocs C B
    · have hΦ : (t, p) ∈ B ∪ predLocs C B := Finset.mem_union_right _ hP
      unfold fS; dsimp only; rw [if_pos hΦ]
      rw [hfault]
      unfold designCh
      rw [if_neg hB, applyKraus_comp, applyKraus_lift, castAdd_trans]
      unfold Vc
      rw [ideal_W m l.support _ T' hnotT]
      obtain ⟨T'', hT'', heq⟩ := swaps_W m l.support (flags C B t p l) (flags_nodup C B t p l)
        T' (applyKraus (l.support.trans Function.Embedding.inl) l.op.idealKraus
          (if ∃ j < p, (t, j) ∈ B then applyJ m (J t) (pendX m J (pend C B t) σ) else σ))
      refine ⟨T'', hupd T'' hT'', ?_⟩
      rw [heq, hX]
    · have hΦ : (t, p) ∉ B ∪ predLocs C B := by
        rw [Finset.mem_union]; tauto
      unfold fS; dsimp only; rw [if_neg hΦ]
      have hfl : (flags C B t p l).map l.support = [] := by
        rw [List.map_eq_nil_iff, List.eq_nil_iff_forall_not_mem]
        intro i hi
        rw [flags_mem, if_neg hB] at hi
        exact hP (pred_of_bad C B t ht p hp i hi)
      refine ⟨T', hupd T' (by intro q; rw [hfl]; simp), ?_⟩
      unfold Vc
      rw [ideal_W m l.support _ T' hnotT, hX]

end Main2

section Main3
variable {Q : Type} [Fintype Q] [DecidableEq Q] (C : Circuit Q) (m : ℕ)
  (B : Finset (ℕ × ℕ)) (J : ℕ → JointFault Q m)
  (hJ : ∀ t i, (J t).supp i ∈ badQubits C B t)
include hJ

private lemma layer_step (t : ℕ) (ht : t < C.length) (ρ : Op (Q ⊕ Fin m)) :
    ∃ ρ' : Op (Q ⊕ Fin m),
      faultyLayer (B ∪ predLocs C B) (faultD C m B J) t C[t] (Vc m (badQubits C B t) ρ) =
        Vc m (badQubits C B (t + 1)) ρ' ∧
      jointLayer B (J t) t C[t] (pendX m J (pend C B t) ρ) =
        pendX m J (pend C B (t + 1)) ρ' := by
  classical
  have hfold := fold2 C[t].locs 0 (fJ m B t) (fS C m B J t)
    (fun p σ σS => ∃ T' : Set Q, (∀ q, q ∈ T' ↔ (q ∈ badQubits C B t ↔ ¬ ∃ (j : ℕ)
        (hj : j < C[t].locs.length),
        j < p ∧ q ∈ (flags C B t j C[t].locs[j]).map C[t].locs[j].support)) ∧
       σS = Vc m T' (if ∃ j < p, (t, j) ∈ B then
         applyJ m (J t) (pendX m J (pend C B t) σ) else σ))
    ρ (Vc m (badQubits C B t) ρ) ⟨badQubits C B t, by simp, by simp⟩ (by
      intro p hp σ σS ⟨T', hT', hσS⟩
      simp only [Nat.zero_add] at hT' hσS ⊢
      obtain ⟨T'', hT'', heq⟩ := inner_step C m B J hJ t ht p hp σ T' hT'
      exact ⟨T'', hT'', by rw [hσS]; exact heq⟩)
  simp only [Nat.zero_add] at hfold
  obtain ⟨T', hT', heq⟩ := hfold
  have hTe : T' = badQubits C B (t + 1) := by
    ext q
    rw [hT']
    obtain ⟨j0, hj0, i0, hi0⟩ := layer_cover C[t] q
    have key : (∃ (j : ℕ) (hj : j < C[t].locs.length), j < C[t].locs.length ∧
        q ∈ (flags C B t j C[t].locs[j]).map C[t].locs[j].support) ↔
        i0 ∈ flags C B t j0 C[t].locs[j0] := by
      constructor
      · rintro ⟨j, hj, _, hq⟩
        obtain ⟨a, ha, hqa⟩ := List.mem_map.1 hq
        have := layer_unique C[t] j j0 hj hj0 q ⟨a, hqa⟩ ⟨i0, hi0⟩
        subst this
        have : a = i0 := C[t].locs[j].support.injective (hqa.trans hi0.symm)
        rwa [← this]
      · intro h
        exact ⟨j0, hj0, hj0, List.mem_map.2 ⟨i0, h, hi0⟩⟩
    rw [key, flags_mem]
    by_cases hB0 : (t, j0) ∈ B
    · have hb : q ∈ badQubits C B t := hi0 ▸ bad_of_mem C B t ht j0 hj0 hB0 i0
      rw [if_pos hB0, ← hi0]
      rw [← hi0] at hb
      tauto
    · have hb : q ∉ badQubits C B t := hi0 ▸ not_bad_of_notin C B t ht j0 hj0 hB0 i0
      rw [if_neg hB0, ← hi0]
      rw [← hi0] at hb
      tauto
  subst hTe
  have hne : (∃ j < C[t].locs.length, (t, j) ∈ B) ↔ (badQubits C B t).Nonempty :=
    (bad_nonempty_iff C B t ht).symm
  have hcommF : C[t].locs.zipIdx.foldl (fJ m B t) (pendX m J (pend C B t) ρ) =
      pendX m J (pend C B t) (C[t].locs.zipIdx.foldl (fJ m B t) ρ) := by
    symm
    apply fold_comm
    intro σ a
    unfold fJ
    split_ifs
    · rfl
    · exact (comm_ideal_pend C m B J hJ a.1.support _ t (pend C B t) (fun _ h => h) σ).symm
  refine ⟨if (badQubits C B t).Nonempty then
      applyJ m (J t) (pendX m J (pend C B t) (C[t].locs.zipIdx.foldl (fJ m B t) ρ))
    else C[t].locs.zipIdx.foldl (fJ m B t) ρ, ?_, ?_⟩
  · show C[t].locs.zipIdx.foldl (fS C m B J t) _ = _
    rw [heq]
    congr 1
    exact if_congr hne rfl rfl
  · show applyJ m (J t) (C[t].locs.zipIdx.foldl (fJ m B t) _) = _
    rw [hcommF]
    simp only [pend]
    split_ifs with h
    · rfl
    · simp [pendX, List.foldl_append]

omit hJ in
private lemma Vc_init (T : Set Q) :
    Vc m T (initState (Q ⊕ Fin m)) = initState (Q ⊕ Fin (m + Fintype.card Q)) := by
  classical
  ext x y
  unfold Vc
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Q ⊕ Fin m → Fin 2)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Q ⊕ Fin m → Fin 2)]
    · simp only [Matrix.conjTranspose_apply, Wm, initState, embT_zero, and_self, if_true,
        mul_one]
      by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
    · intro b _ hb; simp [initState, hb]
    · simp
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero]
    · simp
    · intro a _; simp [initState, hb]
  · simp

end Main3

theorem solution {Q : Type} [Fintype Q] [DecidableEq Q] (C : Circuit Q) (m : ℕ) :
    ∃ m' : ℕ, ∀ (B : Finset (ℕ × ℕ)) (J : ℕ → JointFault Q m),
      (∀ t i, (J t).supp i ∈ badQubits C B t) →
      ∃ fault' : ℕ → ℕ → (k : ℕ) → Channel (k + m'),
        dataOutDist (jointFaultyState B J C) =
          dataOutDist (faultyState (B ∪ predLocs C B) fault' C) := by
  classical
  refine ⟨m + Fintype.card Q, fun B J hJ => ⟨faultD C m B J, ?_⟩⟩
  have hfold := fold2 C 0 (fun σ Lt => jointLayer B (J Lt.2) Lt.2 Lt.1 σ)
    (fun σ Lt => faultyLayer (B ∪ predLocs C B) (faultD C m B J) Lt.2 Lt.1 σ)
    (fun t ρJ ρS => ∃ ρ, ρS = Vc m (badQubits C B t) ρ ∧ ρJ = pendX m J (pend C B t) ρ)
    (initState _) (initState _) ⟨initState _, (Vc_init m _).symm, rfl⟩ (by
      intro p hp ρJ ρS ⟨ρ, hS, hJρ⟩
      simp only [Nat.zero_add] at hS hJρ ⊢
      obtain ⟨ρ', h1, h2⟩ := layer_step C m B J hJ p hp ρ
      exact ⟨ρ', by rw [hS]; exact h1, by rw [hJρ]; exact h2⟩)
  simp only [Nat.zero_add] at hfold
  obtain ⟨ρ, hS, hJρ⟩ := hfold
  show dataOutDist (C.zipIdx.foldl _ _) = dataOutDist (C.zipIdx.foldl _ _)
  rw [hS, hJρ]
  rw [dataOut_pendX C m B J hJ C.length (pend C B C.length) (fun _ h => h)]
  unfold Vc
  rw [dataOut_W _ (embT_inj m _) (fun z q => by
    rw [embT_inl, if_neg (bad_empty_of_ge C B C.length le_rfl q)])]

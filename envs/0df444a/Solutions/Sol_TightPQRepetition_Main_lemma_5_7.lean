-- Prove2me | solution 1 for TightPQRepetition.Main.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T15:30:47.344798+00:00
-- url     : https://prove2.me/submissions/574a34e8-e6a4-4bf1-bb13-30efcd99fdd6

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Reduction

namespace TightPQRepetition.Main
open QAlgorithms Matrix
open scoped ComplexConjugate Classical

theorem embedOp_unitary {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (hM : Mᴴ * M = 1)
    (w : Fin k ↪ Fin n) : (embedOp M w)ᴴ * embedOp M w = 1 := by
  ext y z
  have hM' : ∀ a b, ∑ u, star (M u a) * M u b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hM a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, embedOp, Matrix.of_apply,
    Matrix.one_apply]
  by_cases B : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · have key : ∀ x : Qubits n, (∀ a : Fin n, a ∉ Set.range w → x a = z a) ↔
        (∀ a : Fin n, a ∉ Set.range w → x a = y a) := by
      intro x
      constructor
      · intro h a ha; rw [h a ha, B a ha]
      · intro h a ha; rw [h a ha, B a ha]
    have e1 : ∀ x : Qubits n, star (if ∀ a : Fin n, a ∉ Set.range w → x a = y a then M (x ∘ ⇑w) (y ∘ ⇑w) else 0) *
        (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then M (x ∘ ⇑w) (z ∘ ⇑w) else 0) =
        if ∀ a : Fin n, a ∉ Set.range w → x a = y a then star (M (x ∘ ⇑w) (y ∘ ⇑w)) * M (x ∘ ⇑w) (z ∘ ⇑w) else 0 := by
      intro x
      by_cases h : ∀ a : Fin n, a ∉ Set.range w → x a = y a
      · rw [if_pos h, if_pos h, if_pos ((key x).2 h)]
      · rw [if_neg h, if_neg h]; simp
    simp only [e1]
    rw [← Finset.sum_filter]
    have hb : ∑ x ∈ Finset.univ.filter (fun x : Qubits n => ∀ a : Fin n, a ∉ Set.range w → x a = y a),
        star (M (x ∘ ⇑w) (y ∘ ⇑w)) * M (x ∘ ⇑w) (z ∘ ⇑w) =
        ∑ u : Qubits k, star (M u (y ∘ ⇑w)) * M u (z ∘ ⇑w) := by
      refine Finset.sum_bij (fun x _ => x ∘ ⇑w) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro x hx x' hx' h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
        funext a
        by_cases ha : a ∈ Set.range w
        · obtain ⟨i, rfl⟩ := ha
          exact congrFun h i
        · rw [hx a ha, hx' a ha]
      · intro u _
        refine ⟨fun a => if h : ∃ i, w i = a then u h.choose else y a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro a ha
          have : ¬ ∃ i, w i = a := fun ⟨i, hi⟩ => ha ⟨i, hi⟩
          simp [this]
        · funext i
          have h : ∃ j, w j = w i := ⟨i, rfl⟩
          simp only [Function.comp, h, dite_true]
          rw [w.injective h.choose_spec]
      · intro x _; rfl
    rw [hb, hM']
    have : (y ∘ ⇑w = z ∘ ⇑w) ↔ y = z := by
      constructor
      · intro h; funext a
        by_cases ha : a ∈ Set.range w
        · obtain ⟨i, rfl⟩ := ha
          exact congrFun h i
        · exact B a ha
      · intro h; rw [h]
    simp only [this]
  · have hz : ∀ x : Qubits n, star (if ∀ a : Fin n, a ∉ Set.range w → x a = y a then M (x ∘ ⇑w) (y ∘ ⇑w) else 0) *
        (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then M (x ∘ ⇑w) (z ∘ ⇑w) else 0) = 0 := by
      intro x
      by_cases h1 : ∀ a : Fin n, a ∉ Set.range w → x a = y a
      · by_cases h2 : ∀ a : Fin n, a ∉ Set.range w → x a = z a
        · exact absurd (fun a ha => (h1 a ha).symm.trans (h2 a ha)) B
        · rw [if_neg h2]; simp
      · rw [if_neg h1]; simp
    simp only [hz, Finset.sum_const_zero]
    have : y ≠ z := fun h => B (fun a _ => by rw [h])
    simp [this]

theorem mem_unitary_of_star_mul {n : Type*} [Fintype n] [DecidableEq n] (a : Matrix n n ℂ)
    (h : aᴴ * a = 1) : a ∈ unitary (Matrix n n ℂ) :=
  ⟨h, mul_eq_one_comm.1 h⟩

theorem circuit_unitary_mem {n : ℕ} (c : QCircuit n) :
    c.unitary ∈ unitary (Matrix (Qubits n) (Qubits n) ℂ) := by
  unfold Circuit.unitary
  apply Submonoid.list_prod_mem
  intro a ha
  simp only [List.mem_reverse, List.mem_map] at ha
  obtain ⟨g, _, rfl⟩ := ha
  apply mem_unitary_of_star_mul
  apply embedOp_unitary
  have h := g.mem.2
  have h2 : g.gate.mat ∈ Matrix.unitaryGroup (Qubits g.gate.arity) ℂ := h
  exact (Matrix.mem_unitaryGroup_iff'.1 h2)

theorem flipMask_not_mem {n : ℕ} (w : List (Fin n)) (x : Bits) (a : Fin n) (ha : a ∉ w) :
    flipMask w x a = false := by
  unfold flipMask
  rw [List.any_eq_false]
  intro p hp
  have := List.of_mem_zip hp
  have h1 : p.1 ≠ a := fun h => ha (h ▸ this.1)
  simp [h1]

theorem op_apply {n : ℕ} (s : RoundStep n) (x : Bits) (a b : Qubits n) :
    s.op x a b = s.circ.unitary a (fun i => xor (b i) (flipMask s.inW x i)) := by
  unfold RoundStep.op loadX
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

namespace RedCtx
variable (x : RedCtx)

theorem fullQuery_congr (rv : x.RVer) (e : Bits) (ℓ : ℕ) (w w' : x.Wq)
    (h : ∀ a < ℓ, x.zAt w a = x.zAt w' a) : x.fullQuery rv e ℓ w = x.fullQuery rv e ℓ w' := by
  unfold fullQuery internalMsg
  congr 2
  apply List.ofFn_inj.2
  funext i
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [h a (List.mem_range.1 ha)]

theorem mask_key (hN : x.B.IsNormalForm x.m) (rv : x.RVer) (ℓ : Fin x.m) (e : Bits)
    (w' w'' : x.Wq) :
    (fun i => xor (w' i) (flipMask (x.B.stepAt ℓ).inW (x.fullQuery rv e ℓ w') i)) =
      (fun i => xor (w'' i) (flipMask (x.B.stepAt ℓ).inW (x.fullQuery rv e ℓ w'') i)) ↔
    w' = w'' := by
  constructor
  · intro h
    have hoff : ∀ a, a ∉ (x.B.stepAt ℓ).inW → w' a = w'' a := by
      intro a ha
      have := congrFun h a
      simpa [flipMask_not_mem _ _ a ha] using this
    have hz : ∀ a < (ℓ : ℕ), x.zAt w' a = x.zAt w'' a := by
      intro a ha
      unfold zAt
      apply List.map_congr_left
      intro b hb
      apply hoff
      exact (hN.2.2.2.2 ℓ a ℓ.2 (by omega) (by omega) b hb).2.1
    have hq := x.fullQuery_congr rv e ℓ w' w'' hz
    rw [hq] at h
    funext i
    have := congrFun h i
    revert this
    cases w' i <;> cases w'' i <;> cases flipMask (x.B.stepAt ℓ).inW (x.fullQuery rv e ℓ w'') i <;> simp
  · intro h; subst h; rfl

theorem uVer_unitary (hN : x.B.IsNormalForm x.m) (rv : x.RVer) (ℓ : Fin x.m) :
    (x.uVer rv ℓ)ᴴ * x.uVer rv ℓ = 1 := by
  have hU := (Unitary.mem_iff.1 (circuit_unitary_mem (x.B.stepAt ℓ).circ)).1
  have hU' : ∀ a b : Qubits x.B.n, ∑ u, star ((x.B.stepAt ℓ).circ.unitary u a) *
      (x.B.stepAt ℓ).circ.unitary u b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hU a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  ext ⟨w', y'⟩ ⟨w'', y''⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, uVer, Matrix.of_apply,
    Matrix.one_apply]
  by_cases h2 : y' = y''
  · subst h2
    rw [Fintype.sum_prod_type]
    simp only [op_apply]
    simp only [Prod.mk.injEq, and_true]
    have : ∀ a : x.Wq, ∑ y : x.RE, star (if y = y' then (x.B.stepAt ℓ).circ.unitary a
          (fun i => xor (w' i) (flipMask (x.B.stepAt ℓ).inW (x.fullQuery rv (toBits (y'.2 ℓ)) ℓ w') i)) else 0) *
        (if y = y' then (x.B.stepAt ℓ).circ.unitary a
          (fun i => xor (w'' i) (flipMask (x.B.stepAt ℓ).inW (x.fullQuery rv (toBits (y'.2 ℓ)) ℓ w'') i)) else 0) =
        star ((x.B.stepAt ℓ).circ.unitary a
          (fun i => xor (w' i) (flipMask (x.B.stepAt ℓ).inW (x.fullQuery rv (toBits (y'.2 ℓ)) ℓ w') i))) *
        ((x.B.stepAt ℓ).circ.unitary a
          (fun i => xor (w'' i) (flipMask (x.B.stepAt ℓ).inW (x.fullQuery rv (toBits (y'.2 ℓ)) ℓ w'') i))) := by
      intro a
      rw [Finset.sum_eq_single y']
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [Finset.sum_congr rfl (fun a _ => this a), hU']
    exact if_congr (x.mask_key hN rv ℓ _ w' w'') rfl rfl
  · have hne : ¬ ((w', y') = (w'', y'')) := fun h => h2 (Prod.mk.inj h).2
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    rintro ⟨a, y⟩ _
    by_cases h1 : y = y'
    · have : y ≠ y'' := fun h => h2 (h1 ▸ h)
      simp [this]
    · simp [h1]


theorem uChain_unitary (hN : x.B.IsNormalForm x.m) (rv : x.RVer) (rnd : ℕ) :
    (x.uChain rv rnd)ᴴ * x.uChain rv rnd = 1 := by
  have : x.uChain rv rnd ∈ unitary (Matrix x.Sp x.Sp ℂ) := by
    unfold uChain
    apply Submonoid.list_prod_mem
    intro a ha
    simp only [List.mem_reverse, List.mem_map] at ha
    obtain ⟨ℓ, _, rfl⟩ := ha
    exact mem_unitary_of_star_mul _ (x.uVer_unitary hN rv ℓ)
  exact (Unitary.mem_iff.1 this).1

theorem piVer_proj (rv : x.RVer) : (x.piVer rv)ᴴ = x.piVer rv ∧ x.piVer rv * x.piVer rv = x.piVer rv := by
  unfold piVer
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; split_ifs <;> simp
    · simp [hij, Ne.symm hij]
  · rw [Matrix.diagonal_mul_diagonal]
    apply congrArg
    funext s
    split_ifs <;> simp

theorem piAcc_proj (hN : x.B.IsNormalForm x.m) (rv : x.RVer) (rnd : ℕ) :
    (x.piAcc rv rnd)ᴴ = x.piAcc rv rnd ∧ x.piAcc rv rnd * x.piAcc rv rnd = x.piAcc rv rnd := by
  have hu := x.uChain_unitary hN rv rnd
  have hu' : x.uChain rv rnd * (x.uChain rv rnd)ᴴ = 1 := mul_eq_one_comm.1 hu
  obtain ⟨h1, h2⟩ := x.piVer_proj rv
  unfold piAcc
  constructor
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h1, Matrix.mul_assoc]
  · calc (x.uChain rv rnd)ᴴ * x.piVer rv * x.uChain rv rnd * ((x.uChain rv rnd)ᴴ * x.piVer rv * x.uChain rv rnd)
        = (x.uChain rv rnd)ᴴ * x.piVer rv * (x.uChain rv rnd * (x.uChain rv rnd)ᴴ) * x.piVer rv * x.uChain rv rnd := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hu', Matrix.mul_one]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (x.piVer rv), h2]

end RedCtx

section rot
variable {S : Type} [Fintype S] [DecidableEq S]

theorem cNot_unitary (P : Matrix S S ℂ) (h1 : Pᴴ = P) (h2 : P * P = P) :
    cNot P ∈ unitary (Matrix (Fin 2) (Fin 2) (Matrix S S ℂ)) := by
  have hs : star (cNot P) = cNot P := by
    refine Matrix.ext fun i j => ?_
    have h1' : star P = P := h1
    have h3 : star (1 - P) = 1 - P := by rw [star_sub, star_one, h1']
    fin_cases i <;> fin_cases j <;> simp [cNot, Matrix.conjTranspose_apply, h1', h3]
  have hm : cNot P * cNot P = 1 := by
    have h4 : (1 - P) * (1 - P) + P * P = 1 := by noncomm_ring; rw [h2]; abel
    have h5 : (1 - P) * P + P * (1 - P) = 0 := by noncomm_ring; rw [h2]; abel
    have h7 : P * P + (1 - P) * (1 - P) = 1 := by rw [add_comm]; exact h4
    have h6 : P * (1 - P) + (1 - P) * P = 0 := by rw [add_comm]; exact h5
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [cNot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, h4, h5, h6, h7]
  rw [Unitary.mem_iff, hs]
  exact ⟨hm, hm⟩


theorem gate_unitary (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    g.map (algebraMap ℂ (Matrix S S ℂ)) ∈ unitary (Matrix (Fin 2) (Fin 2) (Matrix S S ℂ)) := by
  let f := algebraMap ℂ (Matrix S S ℂ)
  have hs : star (g.map f) = (star g).map f := by
    refine Matrix.ext fun i j => ?_
    exact (algebraMap_star_comm (R := ℂ) (A := Matrix S S ℂ) (g j i)).symm
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hg
  have h2 : g * star g = 1 := Matrix.mem_unitaryGroup_iff.1 hg
  have hm : ∀ a b : Matrix (Fin 2) (Fin 2) ℂ, a.map f * b.map f = (a * b).map f := by
    intro a b
    exact ((algebraMap ℂ (Matrix S S ℂ)).mapMatrix.map_mul a b).symm
  rw [Unitary.mem_iff, hs, hm, hm, h1, h2]
  have : (1 : Matrix (Fin 2) (Fin 2) ℂ).map f = 1 := (algebraMap ℂ (Matrix S S ℂ)).mapMatrix.map_one
  exact ⟨this, this⟩

theorem programOp_unitary (PA PB : Matrix S S ℂ) (hA : PAᴴ = PA ∧ PA * PA = PA)
    (hB : PBᴴ = PB ∧ PB * PB = PB) (p : RotationProgram)
    (hg : ∀ g, RotationInstr.gate g ∈ p → g ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    programOp PA PB p ∈ unitary (Matrix (Fin 2) (Fin 2) (Matrix S S ℂ)) := by
  unfold programOp
  apply Submonoid.list_prod_mem
  intro a ha
  simp only [List.mem_reverse, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  cases i with
  | callA => exact cNot_unitary _ hA.1 hA.2
  | callB => exact cNot_unitary _ hB.1 hB.2
  | gate g => exact gate_unitary g (hg g hi)

/-- Reading a block matrix `ancilla × ancilla` of operators on `S` as a matrix on `S × ancilla`. -/
def flatten (M : Matrix (Fin 2) (Fin 2) (Matrix S S ℂ)) : Matrix (S × Fin 2) (S × Fin 2) ℂ :=
  Matrix.of fun p q => M p.2 q.2 p.1 q.1

theorem flatten_mul (M N : Matrix (Fin 2) (Fin 2) (Matrix S S ℂ)) :
    flatten (M * N) = flatten M * flatten N := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [flatten, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]
  rw [Finset.sum_comm]

theorem flatten_star (M : Matrix (Fin 2) (Fin 2) (Matrix S S ℂ)) :
    flatten (star M) = (flatten M)ᴴ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [flatten, Matrix.conjTranspose_apply]

theorem flatten_one : flatten (1 : Matrix (Fin 2) (Fin 2) (Matrix S S ℂ)) = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases hij : i = j
  · subst hij; by_cases hab : a = b
    · subst hab; simp [flatten]
    · simp [flatten, hab]
  · simp [flatten, hij, Matrix.one_apply]

theorem flatten_unitary (M : Matrix (Fin 2) (Fin 2) (Matrix S S ℂ))
    (h : M ∈ unitary (Matrix (Fin 2) (Fin 2) (Matrix S S ℂ))) : (flatten M)ᴴ * flatten M = 1 := by
  rw [← flatten_star, ← flatten_mul, (Unitary.mem_iff.1 h).1, flatten_one]

end rot

theorem pack_length (l : List Bits) : (pack l).length = (l.map fun b => 2 * b.length + 1).sum := by
  induction l with
  | nil => simp [pack]
  | cons a l ih =>
    have : pack (a :: l) = packOne a ++ pack l := by simp [pack]
    rw [this, List.length_append, ih]
    simp [packOne, List.length_flatMap]
    ring

theorem zeros_length (n : ℕ) : (zeros n).length = n := by simp [zeros]

theorem toBits_ofBits (n : ℕ) (b : Bits) (h : b.length = n) : toBits (ofBits n b) = b := by
  unfold toBits ofBits
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [h]

theorem toBits_injective {n : ℕ} : Function.Injective (toBits (n := n)) := List.ofFn_injective

namespace RedCtx
variable (x : RedCtx)

theorem msgAt_length (hE : x.E.IsEfficient) (hV : x.V.IsEfficient) (rnd : Fin x.m) (head prev : Bits)
    (hh : head.length = x.V.qLen x.lam rnd) (hp : (rnd : ℕ) = 0 ∨ prev.length = x.E.skLen x.lam)
    (r : x.Rr) (ℓ : Fin x.m) : (x.msgAt rnd head prev r ℓ).length = x.eLen ℓ := by
  have hgen := hE.2.2.2.2.1
  have henc := hE.2.2.2.2.2.1
  have hq : x.eLen ℓ = (pack [zeros (x.E.pkLen x.lam), zeros (x.E.ctLen x.lam (x.V.qLen x.lam ℓ)),
      zeros (if (ℓ : ℕ) = 0 then 0 else x.E.ctLen x.lam (x.E.skLen x.lam))]).length := rfl
  have hvq := hV.2.2.2.1
  have hpl : (if ℓ = rnd then head else zeros (x.V.qLen x.lam ℓ)).length = x.V.qLen x.lam ℓ := by
    split_ifs with h
    · subst h; exact hh
    · exact zeros_length _
  have hsk : (ℓ : ℕ) ≠ 0 → (if ℓ = rnd then prev else
      if h : (ℓ : ℕ) - 1 < x.m then x.skOf (toBits (r ⟨(ℓ : ℕ) - 1, h⟩)) else []).length
        = x.E.skLen x.lam := by
    intro h0
    split_ifs with h h'
    · subst h
      rcases hp with hp | hp
      · exact absurd hp h0
      · exact hp
    · exact (hgen _ _).2
    · exfalso; exact h' (by have := ℓ.2; omega)
  rw [hq]
  unfold msgAt hatMessage
  rw [pack_length, pack_length]
  by_cases h0 : (ℓ : ℕ) = 0
  · rw [h0] at hpl
    simp [h0, zeros_length, hgen, henc, hpl]
  · have := hsk h0
    simp only [h0, if_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp [zeros_length, hgen, henc, hpl, this]

theorem card_part (rnd : Fin x.m) :
    ∑ r : x.Rr, (if (∀ ℓ : Fin x.m, ℓ < rnd → r ℓ = fun _ => false) then (1 : ℝ) else 0)
      = (2 : ℝ) ^ (∑ ℓ : Fin x.m, if rnd ≤ ℓ then x.rLen ℓ else 0) := by
  rw [Finset.sum_boole]
  have : Finset.univ.filter (fun r : x.Rr => ∀ ℓ : Fin x.m, ℓ < rnd → r ℓ = fun _ => false) =
      Fintype.piFinset (fun ℓ : Fin x.m => if ℓ < rnd then ({fun _ => false} : Finset (Qubits (x.rLen ℓ)))
        else Finset.univ) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h ℓ
      by_cases hl : ℓ < rnd
      · simp [hl, h ℓ hl]
      · simp [hl]
    · intro h ℓ hl
      have := h ℓ
      simpa [hl] using this
  rw [this, Fintype.card_piFinset, Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro ℓ _
  by_cases hl : ℓ < rnd
  · simp [hl, not_le.2 hl]
  · simp [hl, not_lt.1 hl]

theorem encState_sum (hE : x.E.IsEfficient) (hV : x.V.IsEfficient) (rnd : Fin x.m) (head prev : Bits)
    (hh : head.length = x.V.qLen x.lam rnd) (hp : (rnd : ℕ) = 0 ∨ prev.length = x.E.skLen x.lam) :
    ∑ y : x.RE, x.encState rnd head prev y * conj (x.encState rnd head prev y) = 1 := by
  set S := ∑ ℓ : Fin x.m, if rnd ≤ ℓ then x.rLen ℓ else 0 with hS
  set a : ℝ := (((Real.sqrt 2) ^ S)⁻¹ : ℝ) with ha
  have ha2 : a ^ 2 = ((2 : ℝ) ^ S)⁻¹ := by
    rw [ha, inv_pow, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  let C : x.RE → Prop := fun p =>
    (∀ ℓ : Fin x.m, ℓ < rnd → p.1 ℓ = (fun _ => false) ∧ p.2 ℓ = (fun _ => false)) ∧
        (∀ ℓ : Fin x.m, rnd ≤ ℓ → toBits (p.2 ℓ) = x.msgAt rnd head prev p.1 ℓ)
  have h1 : ∀ y : x.RE, x.encState rnd head prev y * conj (x.encState rnd head prev y) =
      ((if C y then a ^ 2 else 0 : ℝ) : ℂ) := by
    intro y
    have : x.encState rnd head prev y = if C y then (a : ℂ) else 0 := rfl
    rw [this]
    by_cases hC : C y
    · simp [hC, ← Complex.ofReal_mul, sq]
    · simp [hC]
  simp only [h1]
  rw [← Complex.ofReal_sum]
  let e0 : x.Rr → x.Ee := fun r ℓ =>
    if ℓ < rnd then (fun _ => false) else ofBits (x.eLen ℓ) (x.msgAt rnd head prev r ℓ)
  have hC : ∀ r e, C (r, e) ↔ ((∀ ℓ : Fin x.m, ℓ < rnd → r ℓ = fun _ => false) ∧ e = e0 r) := by
    intro r e
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun ℓ hl => (h1 ℓ hl).1, ?_⟩
      funext ℓ
      by_cases hl : ℓ < rnd
      · simp only [e0, hl, if_true]
        exact (h1 ℓ hl).2
      · simp only [e0, hl, if_false]
        apply toBits_injective
        rw [toBits_ofBits _ _ (x.msgAt_length hE hV rnd head prev hh hp r ℓ)]
        exact h2 ℓ (not_lt.1 hl)
    · rintro ⟨h1, rfl⟩
      refine ⟨fun ℓ hl => ⟨h1 ℓ hl, by simp [e0, hl]⟩, fun ℓ hl => ?_⟩
      simp only [e0, not_lt.2 hl, if_false]
      exact toBits_ofBits _ _ (x.msgAt_length hE hV rnd head prev hh hp r ℓ)
  have hsum : ∑ y : x.RE, (if C y then (1 : ℝ) else 0) = (2 : ℝ) ^ S := by
    rw [Fintype.sum_prod_type, ← x.card_part rnd]
    apply Finset.sum_congr rfl
    intro r _
    simp only [hC]
    by_cases hD : ∀ ℓ : Fin x.m, ℓ < rnd → r ℓ = fun _ => false
    · rw [if_pos hD]
      have : ∀ e : x.Ee, (if ((∀ ℓ : Fin x.m, ℓ < rnd → r ℓ = fun _ => false) ∧ e = e0 r) then (1 : ℝ) else 0)
          = if e = e0 r then 1 else 0 := by
        intro e; split_ifs <;> simp_all
      rw [Finset.sum_congr rfl (fun e _ => this e), Finset.sum_ite_eq']
      simp
    · simp [hD]
  have : ∀ y : x.RE, (if C y then a ^ 2 else 0 : ℝ) = a ^ 2 * (if C y then 1 else 0) := by
    intro y; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun y _ => this y), ← Finset.mul_sum, hsum, ha2]
  have h2 : (2 : ℝ) ^ S ≠ 0 := by positivity
  rw [inv_mul_cancel₀ h2]
  simp

theorem projRE_proj (φ : EuclideanSpace ℂ x.RE) (h : ∑ y : x.RE, φ y * conj (φ y) = 1) :
    (x.projRE φ)ᴴ = x.projRE φ ∧ x.projRE φ * x.projRE φ = x.projRE φ := by
  constructor
  · ext s s'
    by_cases hs : s.1 = s'.1
    · simp [projRE, Matrix.conjTranspose_apply, hs, mul_comm]
    · simp [projRE, Matrix.conjTranspose_apply, hs, Ne.symm hs]
  · ext ⟨w, y⟩ ⟨w', y'⟩
    simp only [Matrix.mul_apply, projRE, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    by_cases hw : w = w'
    · subst hw
      rw [Finset.sum_eq_single w]
      · simp only [if_true]
        have : ∀ z : x.RE, φ y * conj (φ z) * (φ z * conj (φ y')) = φ y * conj (φ y') * (φ z * conj (φ z)) := by
          intro z; ring
        simp only [this, ← Finset.mul_sum, h, mul_one]
      · intro b _ hb
        apply Finset.sum_eq_zero
        intro z _
        simp [Ne.symm hb]
      · simp
    · rw [if_neg hw]
      apply Finset.sum_eq_zero
      intro b _
      apply Finset.sum_eq_zero
      intro z _
      by_cases h1 : w = b
      · subst h1; simp [hw]
      · simp [h1]

theorem epsQ_pos (hl : 1 ≤ x.lam) : 0 < x.epsQ ∧ x.epsQ < 1 := by
  unfold epsQ
  exact ⟨by positivity, pow_lt_one₀ (by norm_num) (by norm_num) (by omega)⟩

theorem delta_pos (c : ℝ) (h : x.Standing c) (hl : 1 ≤ x.lam) : 0 < x.delta ∧ x.delta < 1 := by
  have hk : (1 : ℝ) ≤ x.k := by exact_mod_cast h.one_le.trans h.le_k
  have hm : (1 : ℝ) ≤ x.m := by exact_mod_cast h.rounds
  have hν := h.nu_pos
  have hνk := h.nu_le
  have hmu : 0 < x.mu := by unfold mu; positivity
  have hN : 1 ≤ x.N := by
    unfold N
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    have := Nat.ceil_eq_zero.1 h0
    have h1 : (0 : ℝ) < 20 * (x.k : ℝ) * x.lam / x.ν := by
      have : (1 : ℝ) ≤ x.lam := by exact_mod_cast hl
      positivity
    linarith
  have hN' : (1 : ℝ) ≤ x.N := by exact_mod_cast hN
  have hmu1 : x.mu ≤ 1 / 10 := by
    unfold mu
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_pos (by linarith : (0:ℝ) < x.k) (by linarith : (0:ℝ) < x.m)]
  constructor
  · unfold delta; positivity
  · unfold delta
    rw [div_lt_one (by positivity)]
    nlinarith

theorem rot_unitary (c : ℝ) (h : x.Standing c) (hl : 1 ≤ x.lam) (PB PA : Matrix x.Sp x.Sp ℂ)
    (hA : PAᴴ = PA ∧ PA * PA = PA) (hB : PBᴴ = PB ∧ PB * PB = PB) :
    (x.rot PB PA)ᴴ * x.rot PB PA = 1 := by
  obtain ⟨e1, e2⟩ := x.epsQ_pos hl
  obtain ⟨d1, d2⟩ := x.delta_pos c h hl
  have hg := (h.rotation _ _ e1 e2 d1 d2).1
  have : x.rot PB PA = flatten (programOp PA PB (x.prog x.epsQ x.delta)) := rfl
  rw [this]
  convert flatten_unitary _ (programOp_unitary PA PB hA hB _ hg)

theorem conjOp_inv (A ρ : Matrix x.Tp x.Tp ℂ) (h : Aᴴ * A = 1) : conjOp Aᴴ (conjOp A ρ) = ρ := by
  unfold conjOp
  rw [Matrix.conjTranspose_conjTranspose]
  calc Aᴴ * (A * ρ * Aᴴ) * A = (Aᴴ * A) * ρ * (Aᴴ * A) := by simp only [Matrix.mul_assoc]
    _ = ρ := by rw [h]; simp

theorem afterAccept_eq (c : ℝ) (h : x.Standing c) (hl : 1 ≤ x.lam) (r0 : Fin x.m)
    (hr0 : (r0 : ℕ) = 0) (rq : Qubits (x.V.coins x.lam)) (rv : x.RVer) (ρ : Matrix x.Tp x.Tp ℂ) :
    x.afterAccept .h13 r0 rq rv ρ = x.afterAccept .h14 r0 rq rv ρ := by
  have hq : (x.V.query x.lam (toBits rq) r0 []).length = x.V.qLen x.lam r0 := h.verifier.2.2.2.1 _ _ _ _
  have hsum := x.encState_sum h.scheme h.verifier r0 (x.V.query x.lam (toBits rq) r0 []) [] hq
    (Or.inl hr0)
  have hun := x.rot_unitary c h hl (x.projRE (x.encState r0 (x.V.query x.lam (toBits rq) r0 []) []))
    (x.piAcc rv r0) (x.piAcc_proj h.normal rv r0) (x.projRE_proj _ hsum)
  unfold afterAccept
  simp only [reduceCtorEq, if_false]
  have e := x.conjOp_inv _ ρ hun
  congr 1

theorem attempts_eq (c : ℝ) (h : x.Standing c) (hl : 1 ≤ x.lam) (r0 : Fin x.m)
    (hr0 : (r0 : ℕ) = 0) (rq : Qubits (x.V.coins x.lam)) (s : ℕ) :
    x.attempts .h13 r0 rq s = x.attempts .h14 r0 rq s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    unfold attempts
    simp only [reduceCtorEq, if_false, ih, x.afterAccept_eq c h hl r0 hr0]

end RedCtx
open RedCtx in
theorem lemma_5_7_aux (x : RedCtx) (c : ℝ) (h : x.Standing c) (r0 : Fin x.m)
    (hr0 : (r0 : ℕ) = 0) :
    x.lawTD (x.hybrid .h13 r0) (x.hybrid .h14 r0) = 0 := by
  have : x.hybrid .h13 r0 = x.hybrid .h14 r0 := by
    by_cases hl : 1 ≤ x.lam
    · unfold hybrid
      simp only [x.attempts_eq c h hl r0 hr0]
    · have hlam : x.lam = 0 := by omega
      have hN : x.N = 0 := by simp [RedCtx.N, hlam]
      unfold hybrid
      simp only [hN]
      rfl
  rw [this]
  simp [lawTD]
end TightPQRepetition.Main

theorem solution (x : TightPQRepetition.Main.RedCtx) (c : ℝ) (h : x.Standing c) (r0 : Fin x.m)
    (hr0 : (r0 : ℕ) = 0) :
    x.lawTD (x.hybrid .h13 r0) (x.hybrid .h14 r0) = 0 :=
  TightPQRepetition.Main.lemma_5_7_aux x c h r0 hr0

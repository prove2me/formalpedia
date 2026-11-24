-- Prove2me | solution 1 for TightPQRepetition.Main.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T14:59:00.509187+00:00
-- url     : https://prove2.me/submissions/54e252cb-9c9d-4eb7-b91b-1c648a9a333e

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Reduction

namespace TightPQRepetition.Main
open QAlgorithms Matrix
open scoped ComplexConjugate Classical

namespace RedCtx
variable (x : RedCtx) {c : ℝ}

lemma sum_Tp (w : x.Wq) (o : Fin 2) (F : x.Tp → ℂ) :
    ∑ c : x.Tp, (if c.1.1 = w ∧ c.2 = o then F c else 0) = ∑ z : x.RE, F ((w, z), o) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun c => c.1.2) (fun z => ((w, z), o)) ?_ ?_ ?_ ?_ ?_
  · intro c _; simp
  · intro z _; simp
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨⟨a, b⟩, c⟩ := c
    simp only at hc
    obtain ⟨h1, h2⟩ := hc
    subst h1; subst h2; rfl
  · intro z _; rfl
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨⟨a, b⟩, c⟩ := c
    simp only at hc
    obtain ⟨h1, h2⟩ := hc
    subst h1; subst h2; rfl

lemma proj_entry (φ : EuclideanSpace ℂ x.RE) (X : Matrix x.Tp x.Tp ℂ) (a b : x.Tp) :
    conjOp (x.lift (x.projRE φ)) X a b = φ a.1.2 * conj (φ b.1.2) *
      ∑ z : x.RE, ∑ z' : x.RE, conj (φ z) * X ((a.1.1, z), a.2) ((b.1.1, z'), b.2) * φ z' := by
  obtain ⟨⟨w, y⟩, o⟩ := a
  obtain ⟨⟨w', y'⟩, o'⟩ := b
  have hP : ∀ (w : x.Wq) (y : x.RE) (o : Fin 2) (c : x.Tp), x.lift (x.projRE φ) ((w, y), o) c =
      if c.1.1 = w ∧ c.2 = o then φ y * conj (φ c.1.2) else 0 := by
    rintro w y o ⟨⟨a, b⟩, c⟩
    simp only [lift, projRE, Matrix.of_apply]
    by_cases h1 : a = w <;> by_cases h2 : c = o <;> simp [h1, h2, @eq_comm _ w, @eq_comm _ o]
  have hQ : ∀ d : x.Tp, star (x.lift (x.projRE φ) ((w', y'), o') d) =
      if d.1.1 = w' ∧ d.2 = o' then conj (φ y') * φ d.1.2 else 0 := by
    intro d
    rw [hP]
    split_ifs <;> simp
  simp only [conjOp, Matrix.mul_apply, Matrix.conjTranspose_apply, hQ]
  simp only [hP, ite_mul, zero_mul, Finset.sum_mul]
  simp only [sum_Tp]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, sum_Tp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  ring

lemma proj_absorb (φ : EuclideanSpace ℂ x.RE) (hφ : ∑ y, φ y * conj (φ y) = 1)
    (X : Matrix x.Tp x.Tp ℂ) :
    x.appendRE (x.discardRE (conjOp (x.lift (x.projRE φ)) X)) φ =
      conjOp (x.lift (x.projRE φ)) X := by
  ext ⟨⟨w, y⟩, o⟩ ⟨⟨w', y'⟩, o'⟩
  rw [proj_entry]
  simp only [appendRE, discardRE, Matrix.of_apply, proj_entry]
  rw [← Finset.sum_mul, hφ]
  ring

lemma pack_length_eq (l l' : List Bits) (h : l.map List.length = l'.map List.length) :
    (pack l).length = (pack l').length := by
  have key : ∀ l : List Bits, (pack l).length = ((l.map List.length).map fun n => 2 * n + 1).sum := by
    intro l
    induction l with
    | nil => simp [pack]
    | cons a t ih =>
      have : (pack t).length = _ := ih
      simp only [pack, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at this ⊢
      rw [this]
      simp [packOne, List.length_flatMap]
      omega
  rw [key, key, h]


lemma msgAt_length (h : x.Standing c) (r0 : Fin x.m) (hr0 : (r0 : ℕ) = 0) (head : Bits)
    (hh : head.length = x.V.qLen x.lam r0) (r : x.Rr) (ℓ : Fin x.m) :
    (x.msgAt r0 head [] r ℓ).length = x.eLen ℓ := by
  have hE := h.scheme
  have hgen := hE.2.2.2.2.1
  have henc := hE.2.2.2.2.2.1
  have hq : ∀ ℓ, (x.V.qLen x.lam ℓ) = x.V.qLen x.lam ℓ := fun _ => rfl
  simp only [msgAt, eLen, hat, hatV, hatMessage]
  apply pack_length_eq
  by_cases hl : ℓ = r0
  · have h0 : (ℓ : ℕ) = 0 := by rw [hl]; exact hr0
    simp [hl, hr0, (hgen _ _).1, henc, hh, zeros]
  · have h0 : (ℓ : ℕ) ≠ 0 := by
      intro h'; apply hl; ext; rw [h', hr0]
    have hm : (ℓ : ℕ) - 1 < x.m := lt_of_le_of_lt (Nat.sub_le _ _) ℓ.2
    simp [hl, h0, hm, (hgen _ _).1, (hgen _ _).2, henc, skOf, zeros]

lemma enc_card (h : x.Standing c) (r0 : Fin x.m) (hr0 : (r0 : ℕ) = 0) (head : Bits)
    (hh : head.length = x.V.qLen x.lam r0) :
    (Finset.univ.filter fun p : x.RE => ∀ ℓ : Fin x.m, toBits (p.2 ℓ) = x.msgAt r0 head [] p.1 ℓ).card
      = Fintype.card x.Rr := by
  refine Finset.card_nbij' (fun p => p.1)
    (fun r => (r, fun ℓ => ofBits (x.eLen ℓ) (x.msgAt r0 head [] r ℓ))) ?_ ?_ ?_ ?_
  · intro p _; simp
  · intro r _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    intro ℓ
    have hl := x.msgAt_length h r0 hr0 head hh r ℓ
    unfold toBits ofBits
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  · rintro ⟨r, e⟩ hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp
    simp only [Prod.mk.injEq, true_and]
    funext ℓ
    have hl := x.msgAt_length h r0 hr0 head hh r ℓ
    have := hp ℓ
    rw [← this]
    apply List.ofFn_injective
    rw [← this] at hl
    unfold toBits ofBits
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  · intro r _; rfl


lemma enc_norm (h : x.Standing c) (r0 : Fin x.m) (hr0 : (r0 : ℕ) = 0) (head : Bits)
    (hh : head.length = x.V.qLen x.lam r0) :
    ∑ y, (x.encState r0 head []) y * conj ((x.encState r0 head []) y) = 1 := by
  have hle : ∀ ℓ : Fin x.m, r0 ≤ ℓ := fun ℓ => by rw [Fin.le_def, hr0]; exact Nat.zero_le _
  have hlt : ∀ ℓ : Fin x.m, ¬ ℓ < r0 := fun ℓ => not_lt.2 (hle ℓ)
  set S := ∑ ℓ : Fin x.m, if r0 ≤ ℓ then x.rLen ℓ else 0 with hS
  have hS' : S = ∑ ℓ : Fin x.m, x.rLen ℓ := by simp [hS, hle]
  have hcard : (Fintype.card x.Rr : ℝ) = 2 ^ S := by
    rw [hS']
    simp only [Rr, Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    exact Finset.prod_pow_eq_pow_sum Finset.univ (fun ℓ : Fin x.m => x.rLen ℓ) (2 : ℝ)
  have step : ∀ y : x.RE, (x.encState r0 head []) y * conj ((x.encState r0 head []) y) =
      if (∀ ℓ : Fin x.m, toBits (y.2 ℓ) = x.msgAt r0 head [] y.1 ℓ)
      then ((((2 : ℝ) ^ S)⁻¹ : ℝ) : ℂ) else 0 := by
    intro y
    simp only [encState, WithLp.ofLp_toLp]
    by_cases hC : ∀ ℓ : Fin x.m, toBits (y.2 ℓ) = x.msgAt r0 head [] y.1 ℓ
    · rw [if_pos hC, if_pos ⟨fun ℓ hl => absurd hl (hlt ℓ), fun ℓ _ => hC ℓ⟩]
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      rw [← hS, ← mul_inv, ← sq, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    · rw [if_neg hC, if_neg]
      · simp
      · rintro ⟨_, h2⟩
        exact hC fun ℓ => h2 ℓ (hle ℓ)
  simp only [step]
  rw [← Finset.sum_filter, Finset.sum_const, enc_card x h r0 hr0 head hh, nsmul_eq_mul]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, hcard, mul_inv_cancel₀ (by positivity)]
  simp


lemma after_eq (h : x.Standing c) (r0 : Fin x.m) (hr0 : (r0 : ℕ) = 0)
    (rq : Qubits (x.V.coins x.lam)) (rv : x.RVer) (ρ : Matrix x.Tp x.Tp ℂ) :
    x.afterAccept .h11 r0 rq rv ρ = x.afterAccept .h12 r0 rq rv ρ := by
  have hq : (x.V.query x.lam (toBits rq) r0 []).length = x.V.qLen x.lam r0 :=
    h.verifier.2.2.2.1 _ _ _ _
  have hn := x.enc_norm h r0 hr0 _ hq
  simp only [afterAccept]
  simp only [reduceCtorEq, if_false]
  rw [x.proj_absorb _ hn]

lemma attempts_eq (h : x.Standing c) (r0 : Fin x.m) (hr0 : (r0 : ℕ) = 0)
    (rq : Qubits (x.V.coins x.lam)) (s : ℕ) :
    x.attempts .h11 r0 rq s = x.attempts .h12 r0 rq s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [attempts, ih, x.after_eq h r0 hr0, reduceCtorEq, if_false]

end RedCtx

end TightPQRepetition.Main

open TightPQRepetition.Main in
theorem solution (x : RedCtx) (c : ℝ) (h : x.Standing c) (r0 : Fin x.m)
    (hr0 : (r0 : ℕ) = 0) :
    x.lawTD (x.hybrid .h11 r0) (x.hybrid .h12 r0) = 0 := by
  have : x.hybrid .h11 r0 = x.hybrid .h12 r0 := by
    simp only [RedCtx.hybrid, x.attempts_eq h r0 hr0]
  simp [RedCtx.lawTD, this]

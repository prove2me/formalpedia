-- Prove2me | solution 1 for SingleInteraction.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T15:44:47.292468+00:00
-- url     : https://prove2.me/submissions/dd9abee1-23f4-4c11-8b3f-e4979458815b

import Definitions.Def_SingleInteraction_Gadget_H2eff


set_option autoImplicit false
set_option maxHeartbeats 500000

namespace SingleInteraction
namespace DiagonalProof

def zsign (a : Fin 2) : ℂ := if a=0 then 1 else -1

lemma h_symmetric_entries (a b c d : Fin 2) :
    hSIH ![a,b] ![c,d]+hSIH ![b,a] ![d,c]=
      if a=c ∧ b=d then 2*zsign a*zsign b else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [hSIH,twoQubit,MIPRE.LCS.Pauli.X,MIPRE.LCS.Pauli.Y,MIPRE.LCS.Pauli.Z,zsign]

lemma comp_pair {ι α : Type*} (s : ι → α) (u v : ι) : s ∘ ![u,v]=![s u,s v] := by
  funext i
  fin_cases i <;> rfl

lemma symmetric_edge {ι : Type*} [Fintype ι] [DecidableEq ι] (u v : ι) :
    onTuple hSIH ![u,v]+onTuple hSIH ![v,u]=
      Matrix.diagonal (fun s : ι → Fin 2 => 2*zsign (s u)*zsign (s v)) := by
  classical
  apply Matrix.ext
  intro s t
  let off := ∀ i,i≠u → i≠v → s i=t i
  have h1 : (∀ i,(∀ j : Fin 2,(![u,v] : Fin 2 → ι) j≠i) → s i=t i)↔off := by
    simp only [Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,ne_comm,off,and_imp]
  have h2 : (∀ i,(∀ j : Fin 2,(![v,u] : Fin 2 → ι) j≠i) → s i=t i)↔off := by
    simp only [Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,ne_comm,off,and_imp]
    aesop
  simp only [Matrix.add_apply,onTuple,comp_pair,h1,h2,← add_mul,h_symmetric_entries]
  by_cases hst : s=t
  · subst t
    simp [off]
  · have hdiag : ¬(s u=t u ∧ s v=t v) ∨ ¬off := by
      by_contra hn
      push Not at hn
      apply hst
      funext i
      by_cases hu : i=u
      · simpa [hu] using hn.1.1
      by_cases hv : i=v
      · simpa [hv] using hn.1.2
      · exact hn.2 i hu hv
    rcases hdiag with hd | ho
    · simp [hd,Matrix.diagonal_apply,hst]
    · simp [ho,Matrix.diagonal_apply,hst]

lemma insertCore_injective (G : Gadget) (z : G.CoreConfig) : Function.Injective (G.insertCore z) := by
  intro s t h
  funext i
  cases i with
  | inl i => exact congrFun h (G.work i)
  | inr c => exact congrFun h (G.med c)

lemma compression_entry (G : Gadget) (z : G.CoreConfig)
    (A : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ) (s t : G.VS → Fin 2) :
    G.comp z A s t=A (G.insertCore z s) (G.insertCore z t) := by
  simp [Gadget.comp,Matrix.mul_apply,Gadget.iso,Matrix.conjTranspose_apply]

lemma compression_diagonal (G : Gadget) (z : G.CoreConfig) (f : (G.Qb → Fin 2) → ℂ) :
    G.comp z (Matrix.diagonal f)=Matrix.diagonal (fun s => f (G.insertCore z s)) := by
  classical
  apply Matrix.ext
  intro s t
  rw [compression_entry]
  simp only [Matrix.diagonal_apply,(insertCore_injective G z).eq_iff]

lemma compression_add (G : Gadget) (z : G.CoreConfig)
    (A B : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ) :
    G.comp z (A+B)=G.comp z A+G.comp z B := by
  apply Matrix.ext
  intro s t
  simp only [compression_entry,Matrix.add_apply]

lemma compression_sub (G : Gadget) (z : G.CoreConfig)
    (A B : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ) :
    G.comp z (A-B)=G.comp z A-G.comp z B := by
  apply Matrix.ext
  intro s t
  simp only [compression_entry,Matrix.sub_apply]

lemma compression_smul (G : Gadget) (z : G.CoreConfig) (c : ℂ)
    (A : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ) :
    G.comp z (c • A)=c • G.comp z A := by
  apply Matrix.ext
  intro s t
  simp only [compression_entry,Matrix.smul_apply]

lemma compression_sum (G : Gadget) (z : G.CoreConfig) {ι : Type*} (is : Finset ι)
    (A : ι → Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ) :
    G.comp z (∑ i ∈ is,A i)=∑ i ∈ is,G.comp z (A i) := by
  apply Matrix.ext
  intro s t
  simp only [compression_entry,Matrix.sum_apply]

lemma compression_one (G : Gadget) (z : G.CoreConfig) : G.comp z 1=1 := by
  apply Matrix.ext
  intro s t
  simp only [compression_entry,Matrix.one_apply,(insertCore_injective G z).eq_iff]

end DiagonalProof
end SingleInteraction


set_option autoImplicit false
set_option maxHeartbeats 500000

namespace SingleInteraction.DiagonalProof

lemma core_compressed (G : Gadget) : G.comp G.zval G.Hcore=
    (-2*(G.S : ℂ)^2) • (1 : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ) := by
  unfold Gadget.Hcore
  simp_rw [symmetric_edge,compression_sum,compression_diagonal]
  apply Matrix.ext
  intro s t
  simp only [Matrix.sum_apply]
  simp [Matrix.sum_apply,Gadget.insertCore,Gadget.zval,Gadget.coreA,Gadget.coreB,zsign,
    Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply]
  split_ifs <;> simp_all
  <;> ring

lemma mediator_anchor_value (G : Gadget) (c : G.Med) (t : G.VS → Fin 2) (x : Fin G.S) :
    2*zsign (G.insertCore G.zval t (G.med c))*zsign (G.insertCore G.zval t (G.anchor c x))=
      4*(if t (Sum.inr c)=G.bpref c then (0 : ℂ) else 1)-2 := by
  rcases c with ⟨e,g,r⟩
  generalize h : t (Sum.inr (e,g,r))=b
  cases g <;> fin_cases b <;>
    norm_num [Gadget.insertCore,Gadget.zval,Gadget.med,Gadget.anchor,Gadget.coreA,Gadget.coreB,
      Gadget.bpref,zsign,h]

lemma anchor_compressed (G : Gadget) : G.comp G.zval G.Hanchor=
    (4*(G.L : ℂ)) • G.Ncount+(-4*(G.M : ℂ)*(G.R : ℂ)*(G.L : ℂ)) • 1 := by
  unfold Gadget.Hanchor
  simp_rw [symmetric_edge,compression_sum,compression_diagonal]
  apply Matrix.ext
  intro s t
  simp only [Matrix.sum_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Gadget.Ncount,Gadget.Pi,Matrix.one_apply]
  by_cases hst : s=t
  · subst t
    simp only [ite_true,mediator_anchor_value,Finset.sum_const,Finset.card_univ,
      G.card_Γ,nsmul_eq_mul,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    simp only [Finset.mul_sum,Finset.sum_mul,mul_sub,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
      nsmul_eq_mul]
    push_cast
    ring
  · simp [hst,Matrix.diagonal_apply]

theorem unperturbed_diagonal (G : Gadget) : G.H0v=(4*(G.L : ℂ)) • G.Ncount := by
  unfold Gadget.H0v Gadget.H0
  rw [compression_sub,compression_add,compression_smul,compression_one,
    core_compressed,anchor_compressed]
  simp only [Gadget.Ebase]
  push_cast
  module

end SingleInteraction.DiagonalProof


set_option autoImplicit false
set_option maxHeartbeats 500000

namespace SingleInteraction.DiagonalProof
open scoped ComplexOrder

def defects (G : Gadget) (t : G.VS → Fin 2) : ℕ :=
  ∑ c : G.Med,if t (Sum.inr c)=G.bpref c then 0 else 1

lemma defects_zero_iff (G : Gadget) (t : G.VS → Fin 2) :
    defects G t=0 ↔ ∀ c,t (Sum.inr c)=G.bpref c := by
  constructor
  · intro h c
    by_contra hc
    have H : (if t (Sum.inr c)=G.bpref c then (0 : ℕ) else 1)≤defects G t := by
      dsimp only [defects]
      exact Finset.single_le_sum (fun d hd => Nat.zero_le
        (if t (Sum.inr d)=G.bpref d then (0 : ℕ) else 1)) (Finset.mem_univ c)
    simp [hc,h] at H
  · intro h
    simp [defects,h]

lemma ncount_diagonal (G : Gadget) :
    G.Ncount=Matrix.diagonal (fun t => (defects G t : ℂ)) := by
  classical
  apply Matrix.ext
  intro s t
  by_cases hst : s=t
  · subst t
    simp [Gadget.Ncount,Gadget.Pi,Matrix.sum_apply,defects]
  · simp [Gadget.Ncount,Gadget.Pi,Matrix.sum_apply,Matrix.diagonal_apply,hst]

lemma pzero_diagonal (G : Gadget) :
    G.Pzero=Matrix.diagonal (fun t => if defects G t=0 then (1 : ℂ) else 0) := by
  simp only [Gadget.Pzero,defects_zero_iff]

lemma qexc_diagonal (G : Gadget) :
    G.Qexc=Matrix.diagonal (fun t => if defects G t=0 then (0 : ℂ) else 1) := by
  classical
  apply Matrix.ext
  intro s t
  simp only [Gadget.Qexc,pzero_diagonal,Matrix.sub_apply,Matrix.one_apply,Matrix.diagonal_apply]
  split_ifs <;> simp_all

lemma zero_defect_energy (G : Gadget) : G.Pzero*G.H0v*G.Pzero=0 := by
  classical
  rw [unperturbed_diagonal,ncount_diagonal,pzero_diagonal,← Matrix.diagonal_smul,
    Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  apply Matrix.ext
  intro s t
  simp only [Matrix.diagonal_apply,Matrix.zero_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> simp_all

lemma positive_defect_gap (G : Gadget) :
    (G.Qexc*G.H0v*G.Qexc-(4*(G.L : ℂ)) • G.Qexc).PosSemidef := by
  classical
  rw [unperturbed_diagonal,ncount_diagonal,qexc_diagonal,← Matrix.diagonal_smul,
    Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal,← Matrix.diagonal_smul,
    Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro t
  simp only [Pi.sub_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul]
  by_cases h : defects G t=0
  · simp [h]
  · simp only [if_neg h,one_mul,mul_one]
    have hn : 1≤defects G t := Nat.one_le_iff_ne_zero.mpr h
    have hN : (1 : ℂ)≤(defects G t : ℂ) := by exact_mod_cast hn
    have hL : (0 : ℂ)≤4*(G.L : ℂ) := by positivity
    exact sub_nonneg.mpr (le_mul_of_one_le_right hL hN)

theorem equation_32 (G : Gadget) :
    G.H0v=(4*(G.L : ℂ)) • G.Ncount ∧ G.Pzero*G.H0v*G.Pzero=0 ∧
      (G.Qexc*G.H0v*G.Qexc-(4*(G.L : ℂ)) • G.Qexc).PosSemidef :=
  ⟨unperturbed_diagonal G,zero_defect_energy G,positive_defect_gap G⟩

end SingleInteraction.DiagonalProof

open SingleInteraction
open scoped ComplexOrder

theorem solution (G : Gadget) :
    G.H0v = (4 * (G.L : ℂ)) • G.Ncount ∧ G.Pzero * G.H0v * G.Pzero = 0 ∧
      (G.Qexc * G.H0v * G.Qexc - (4 * (G.L : ℂ)) • G.Qexc).PosSemidef  := SingleInteraction.DiagonalProof.equation_32 G

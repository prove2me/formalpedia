-- Prove2me | solution 1 for SensitivityCampaign.reach_source_61141556_strict
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-20T22:22:44.978076+00:00
-- url     : https://prove2.me/submissions/949bf5b6-d6d2-4a9d-beda-8322095b7b14

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate

set_option Elab.async false
set_option linter.all false

/-! Complete source-sensitive Boolean construction and strict exponent improvement.
All new labeling, counting and profile arguments are included.
The sole imported campaign theorem is the public proved finite-certificate theorem.
Historical attribution is retained in the component sources. -/



/- A context-free arithmetic identity.  Its explicit proof was independently
kernel-checked; only this small fact is used in the two large envelope proofs. -/
namespace SensitivityProofArithmetic

theorem sub_two_add_one_explicit (t : Nat) (ht : 2 ≤ t) : t-2+1 = t-1 := by
  have hone : 1 ≤ t-1 := Nat.le_sub_of_add_le ht
  simpa only [Nat.sub_sub] using Nat.sub_add_cancel hone

end SensitivityProofArithmetic

/- Component: RowPatternCountingFast -/
section
/-!
Draft of the generic finite counting step behind the sharper tournament
labeling certificate.  This file has not been compiled in the current
environment: no Lean executable or Mathlib checkout is available here.

There are no `sorry`s, added axioms, native-decision shortcuts, or imported
target theorems.  This is deliberately only the row-pattern counting layer;
the final five-event union bound is a separate obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped Classical BigOperators

namespace SharperRowCounting
noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω]

def smallSubsets (R : Finset Ω) (q : ℕ) : Finset (Finset Ω) :=
  R.powerset.filter (fun s => s.card ≤ q)

def rowPatterns (q d : ℕ) : ℕ :=
  ∑ j : Fin (q + 1), d.choose j.val

/-- Encode a small subset by its size and the corresponding fixed-size
power set.  An upper bound is enough; exact equality is unnecessary. -/
theorem smallSubsets_card_le (R : Finset Ω) (q : ℕ) :
    (smallSubsets R q).card ≤ rowPatterns q R.card := by
  let f : (smallSubsets R q) →
      (Σ j : Fin (q + 1), R.powersetCard j.val) := fun s =>
    ⟨⟨s.val.card, by
        have hs := (Finset.mem_filter.mp s.property).2
        omega⟩,
      ⟨s.val, Finset.mem_powersetCard.mpr
        ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp s.property).1, rfl⟩⟩⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact congrArg
      (fun z : (Σ j : Fin (q + 1), R.powersetCard j.val) =>
        (z.2 : Finset Ω)) h
  have hc := Fintype.card_le_of_injective f hf
  calc
    (smallSubsets R q).card ≤
        Fintype.card (Σ j : Fin (q + 1), R.powersetCard j.val) := by
      simpa only [Fintype.card_coe] using hc
    _ = ∑ j : Fin (q + 1), Fintype.card (R.powersetCard j.val) :=
      Fintype.card_sigma
    _ = rowPatterns q R.card := by
      simp only [rowPatterns, Fintype.card_coe, Finset.card_powersetCard]

def rowUnion (R : ι → Finset Ω) : Finset Ω :=
  Finset.univ.biUnion R

def rowGood (R : ι → Finset Ω) (q : ι → ℕ) (c : Ω → Fin 2) :
    Finset (Ω → Fin 2) :=
  Finset.univ.filter (fun a =>
    ∀ i, ((R i).filter (fun e => a e ≠ c e)).card ≤ q i)

/-- A binary labeling is determined by its values outside all rows and
its mismatch subset in every row.  This bound does not even need disjoint
rows: disjointness enters later when the union size is identified. -/
theorem rowGood_card_le_smallSubsets
    (R : ι → Finset Ω) (q : ι → ℕ) (c : Ω → Fin 2) :
    (rowGood R q c).card ≤
      2 ^ (Fintype.card Ω - (rowUnion R).card) *
        ∏ i, (smallSubsets (R i) (q i)).card := by
  let S := rowUnion R
  let encode : (rowGood R q c) →
      ((Sᶜ : Finset Ω) → Fin 2) ×
        ((i : ι) → smallSubsets (R i) (q i)) := fun a =>
    ⟨fun e => a.val e.val,
      fun i =>
        ⟨(R i).filter (fun e => a.val e ≠ c e),
          Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
              (Finset.mem_filter.mp a.property).2 i⟩⟩⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    funext e
    by_cases he : e ∈ S
    · obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
      have hs := congrArg
        (fun z : ((Sᶜ : Finset Ω) → Fin 2) ×
            ((i : ι) → smallSubsets (R i) (q i)) =>
          (z.2 i : Finset Ω)) hab
      have hm := (Finset.ext_iff.mp hs) e
      simp only [encode, Finset.mem_filter, hei, true_and] at hm
      apply Fin.ext
      have ha := (a.val e).isLt
      have hb := (b.val e).isLt
      have hc := (c e).isLt
      have hm' : ((a.val e).val ≠ (c e).val) ↔
          ((b.val e).val ≠ (c e).val) := by
        simpa only [ne_eq, Fin.ext_iff] using hm
      omega
    · exact congrArg
        (fun z : ((Sᶜ : Finset Ω) → Fin 2) ×
            ((i : ι) → smallSubsets (R i) (q i)) =>
          z.1 ⟨e, Finset.mem_compl.mpr he⟩) hab
  have hc := Fintype.card_le_of_injective encode hencode
  simpa [S, Fintype.card_pi, Finset.card_compl] using hc

/-- The desired product of independent row-pattern upper bounds.  In a
tournament application Ω is all ordered vertex pairs, R i is the set of
internal outgoing arcs from i, and `rowUnion R` has size `choose t 2`. -/
theorem rowGood_card_le
    (R : ι → Finset Ω) (q : ι → ℕ) (c : Ω → Fin 2) :
    (rowGood R q c).card ≤
      2 ^ (Fintype.card Ω - (rowUnion R).card) *
        ∏ i, rowPatterns (q i) (R i).card := by
  refine (rowGood_card_le_smallSubsets R q c).trans ?_
  apply Nat.mul_le_mul_left
  exact Finset.prod_le_prod' (fun i _ => smallSubsets_card_le (R i) (q i))

/-- Algebraic cancellation after multiplying the finite degree-tangent
inequalities.  Here `n` is the number of rows, `a*n+b` their total degree,
and `P` the product of their row-pattern counts. -/
theorem tangent_product_cancel (n a b M N P : ℕ)
    (hb : b ≤ n) (hM : 0 < M) (hN : 0 < N)
    (hprod : P * M ^ (a * n + b) * N ^ (a * n) ≤
      M ^ ((a + 1) * n) * N ^ (a * n + b)) :
    P ≤ M ^ (n - b) * N ^ b := by
  have he : (a + 1) * n = (a * n + b) + (n - b) := by
    calc
      (a + 1) * n = a * n + n := by ring
      _ = (a * n + b) + (n - b) := by omega
  let C := M ^ (a * n + b) * N ^ (a * n)
  have hC : 0 < C := Nat.mul_pos (pow_pos hM _) (pow_pos hN _)
  have hr : M ^ ((a + 1) * n) * N ^ (a * n + b) =
      (M ^ (n - b) * N ^ b) * C := by
    rw [he, pow_add, pow_add]
    dsimp only [C]
    ring
  have hh : P * C ≤ (M ^ (n - b) * N ^ b) * C := by
    simpa only [C, mul_assoc, hr] using hprod
  by_contra hn
  have hlt : M ^ (n - b) * N ^ b < P := Nat.lt_of_not_ge hn
  have hc := Nat.mul_lt_mul_of_pos_right hlt hC
  exact (not_lt_of_ge hh) hc

/-- The product bound needed by the exact certificates: it suffices to check
one tangent inequality at each finite outgoing degree. -/
theorem balanced_product_le (d F : ι → ℕ) (a b M N : ℕ)
    (hb : b ≤ Fintype.card ι) (hM : 0 < M) (hN : 0 < N)
    (hs : ∑ i, d i = a * Fintype.card ι + b)
    (ht : ∀ i, F i * M ^ (d i) * N ^ a ≤ M ^ (a + 1) * N ^ (d i)) :
    ∏ i, F i ≤ M ^ (Fintype.card ι - b) * N ^ b := by
  apply tangent_product_cancel (Fintype.card ι) a b M N (∏ i, F i) hb hM hN
  have hp := Finset.prod_le_prod' (s := Finset.univ) (fun i _ => ht i)
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, hs] at hp
  simpa only [mul_comm a, mul_comm (a + 1)] using hp





end
end SharperRowCounting
end



/- Component: RowLLLArithmeticFast -/
section
/-!
Exact row-count and asymmetric local-lemma activity certificates.
This arithmetic component is used by the full shared-labeling proof.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 4096

namespace SharperRowLLL

def vertices (cfg : Fin 2) : ℕ := ![12605, 12607] cfg

def cutoff (cfg : Fin 2) (q : Fin 5) : ℕ :=
  if cfg.val = 0 then ![23, 31, 38, 44, 50] q
  else ![23, 32, 38, 44, 50] q

def F (q d : ℕ) : ℕ := SharperRowCounting.rowPatterns q d

def lowDegree (cfg : Fin 2) (q : Fin 5) : ℕ := (cutoff cfg q - 1) / 2

def highCount (cfg : Fin 2) (q : Fin 5) : ℕ :=
  (cutoff cfg q).choose 2 - cutoff cfg q * lowDegree cfg q

def lowValue (cfg : Fin 2) (q : Fin 5) : ℕ := F q.val (lowDegree cfg q)
def highValue (cfg : Fin 2) (q : Fin 5) : ℕ := F q.val (lowDegree cfg q + 1)

def balancedProduct (cfg : Fin 2) (q : Fin 5) : ℕ :=
  lowValue cfg q ^ (cutoff cfg q - highCount cfg q) *
    highValue cfg q ^ highCount cfg q




/-- Exact finite tangent inequalities, valid for every possible internal degree. -/
theorem tangent_certificates :
    ∀ (cfg : Fin 2) (q : Fin 5) (d : Fin (cutoff cfg q)),
      F q.val d.val * lowValue cfg q ^ d.val *
        highValue cfg q ^ lowDegree cfg q ≤
      lowValue cfg q ^ (lowDegree cfg q + 1) * highValue cfg q ^ d.val := by
  decide







theorem elementary_bounds :
    ∀ (cfg : Fin 2) (q : Fin 5),
      2 ≤ cutoff cfg q ∧ cutoff cfg q ≤ vertices cfg ∧
      0 < lowValue cfg q ∧ 0 < highValue cfg q ∧
      highCount cfg q ≤ cutoff cfg q ∧
      cutoff cfg q * lowDegree cfg q + highCount cfg q =
        (cutoff cfg q).choose 2 := by
  decide




def tags (cfg : Fin 2) (q : Fin 5) : ℕ :=
  2 ^ cutoff cfg q * balancedProduct cfg q

















end SharperRowLLL
end



/- Component: RawLLLCoreFast -/
section
open scoped Classical BigOperators
namespace SensitivityLabelCache12607

/- Pruned labeling component: TournamentInternalEdgesLabeling -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open scoped Classical BigOperators

namespace OAI.Paper320
noncomputable section
structure Tournament (k : ℕ) extends Digraph (Fin k) where
  loopless : ∀ i, ¬ Adj i i
  edge_compl : ∀ {i j}, i ≠ j → (Adj i j ↔ ¬ Adj j i)

namespace Tournament
variable {k : ℕ} (T : Tournament k)
theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h

theorem not_adj_reverse {i j : Fin k} (h : T.Adj i j) : ¬ T.Adj j i :=
  (T.edge_compl (T.ne_of_adj h)).mp h

theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)

def internalEdges (I : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (I ×ˢ I).filter fun p => T.Adj p.1 p.2

theorem card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by
  let U := T.internalEdges I
  let V := (I ×ˢ I).filter fun p => T.Adj p.2 p.1
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact T.not_adj_reverse (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion V hd = I.offDiag := by
    ext ⟨i,j⟩
    simp only [Finset.mem_disjUnion, U, V, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hi,hj⟩,h⟩ | ⟨⟨hi,hj⟩,h⟩)
      · exact ⟨hi,hj,T.ne_of_adj h⟩
      · exact ⟨hi,hj,(T.ne_of_adj h).symm⟩
    · rintro ⟨hi,hj,hne⟩
      exact (T.adj_or_reverse hne).imp (fun h => ⟨⟨hi,hj⟩,h⟩) (fun h => ⟨⟨hi,hj⟩,h⟩)
  have hs : U.card = V.card := Finset.card_equiv (Equiv.prodComm (Fin k) (Fin k)) (by
    intro p
    simp only [U,V,internalEdges,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

end Tournament
end
end OAI.Paper320

open OAI.Paper320
namespace Sensitivity205
structure Labeling {k : ℕ} (T : Tournament k) (r t : ℕ) where
  label : Fin k → Fin k → Fin r
  coherent_card : ∀ (I : Finset (Fin k)) (m : Fin k → Fin r),
    (∀ i ∈ I, ∀ j ∈ I, T.Adj i j → label i j = m j) → I.card < t

end Sensitivity205


/- Pruned labeling component: DefectBound -/
open OAI.Paper320
namespace SensitivityQ
noncomputable section
def DefectBound {k r : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (q s : ℕ) : Prop :=
  ∀ (S : Finset (Fin k)) (m : Fin k → Fin r),
    (∀ i ∈ S, (S.filter fun j => T.Adj i j ∧ label i j ≠ m j).card ≤ q) →
    S.card < s
end
end SensitivityQ


/- Pruned labeling component: QTagEncoder -/
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205
open scoped Classical BigOperators

namespace SensitivityQ
noncomputable section

def other (c : Fin 2) : Fin 2 := if c = 0 then 1 else 0

theorem eq_other_of_ne (c d : Fin 2) (h : d ≠ c) : d = other c := by
  fin_cases c <;> fin_cases d <;> norm_num [other] at *

/-- Each of q tags marks a wrong outgoing destination; self tags pad a shorter
list. The absence of loops ensures that padding changes no prescribed arc. -/
def good {k q : ℕ} (T : Tournament k) (I : Finset (Fin k))
    (m : I → Fin 2) (e : I → Fin q → I) : Finset (Fin k → Fin k → Fin 2) :=
  Finset.univ.filter fun a => ∀ i j : I, T.Adj i.1 j.1 →
    a i.1 j.1 = if ∃ h, e i h = j then other (m j) else m j

theorem good_card_le {k q : ℕ} (T : Tournament k) (I : Finset (Fin k))
    (m : I → Fin 2) (e : I → Fin q → I) :
    (good T I m e).card ≤ 2 ^ (k*k - I.card.choose 2) := by
  let S := T.internalEdges I
  have hS : S.card = I.card.choose 2 := T.card_internalEdges I
  let f : (Fin k → Fin k → Fin 2) → ((Sᶜ : Finset _) → Fin 2) :=
    fun a p => a p.1.1 p.1.2
  have hinj : Set.InjOn f (good T I m e) := by
    intro a ha b hb hab
    simp only [good, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    funext i j
    by_cases hpair : (i,j) ∈ S
    · simp only [S, Tournament.internalEdges, Finset.mem_filter, Finset.mem_product] at hpair
      obtain ⟨⟨hi,hj⟩,hij⟩ := hpair
      rw [ha ⟨i,hi⟩ ⟨j,hj⟩ hij, hb ⟨i,hi⟩ ⟨j,hj⟩ hij]
    · exact congrFun hab ⟨(i,j), Finset.mem_compl.2 hpair⟩
  calc
    (good T I m e).card ≤ (Finset.univ : Finset ((Sᶜ : Finset _) → Fin 2)).card :=
      Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = 2 ^ (k*k - I.card.choose 2) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Finset.card_compl,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hS]

theorem exists_encoder {k q : ℕ} (T : Tournament k) (I : Finset (Fin k))
    (a : Fin k → Fin k → Fin 2) (m : Fin k → Fin 2)
    (hout : ∀ i ∈ I, (I.filter fun j => T.Adj i j ∧ a i j ≠ m j).card ≤ q) :
    ∃ e : I → Fin q → I, a ∈ good T I (fun j => m j.1) e := by
  let B : Fin k → Finset (Fin k) := fun i =>
    I.filter fun j => T.Adj i j ∧ a i j ≠ m j
  let e : I → Fin q → I := fun i h =>
    if hh : h.val < (B i.1).card then
      let j := (B i.1).equivFin.symm ⟨h.val,hh⟩
      ⟨j.1, (Finset.mem_filter.mp j.2).1⟩
    else i
  have he (i j : I) (hij : T.Adj i.1 j.1) :
      a i.1 j.1 ≠ m j.1 ↔ ∃ h, e i h = j := by
    constructor
    · intro hn
      have hj : j.1 ∈ B i.1 := Finset.mem_filter.mpr ⟨j.2,hij,hn⟩
      let pos := (B i.1).equivFin ⟨j.1,hj⟩
      have hp : pos.val < q := lt_of_lt_of_le pos.isLt (hout i.1 i.2)
      refine ⟨⟨pos.val,hp⟩, ?_⟩
      dsimp only [e]
      rw [dif_pos pos.isLt]
      apply Subtype.ext
      change ((B i.1).equivFin.symm pos).1 = j.1
      exact congrArg (fun z : B i.1 => z.1)
        ((B i.1).equivFin.symm_apply_apply ⟨j.1,hj⟩)
    · rintro ⟨h,hh⟩
      dsimp only [e] at hh
      by_cases hp : h.val < (B i.1).card
      · rw [dif_pos hp] at hh
        let jj := (B i.1).equivFin.symm ⟨h.val,hp⟩
        have hv : jj.1 = j.1 := congrArg Subtype.val hh
        have hn := (Finset.mem_filter.mp jj.2).2.2
        simpa only [hv] using hn
      · rw [dif_neg hp] at hh
        exact False.elim (T.ne_of_adj hij (congrArg Subtype.val hh))
  refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro i j hij
  by_cases hn : a i.1 j.1 ≠ m j.1
  · rw [if_pos ((he i j hij).mp hn)]
    exact eq_other_of_ne _ _ hn
  · rw [if_neg (fun h => hn ((he i j hij).mpr h))]
    exact not_ne_iff.mp hn

end
end SensitivityQ


/- Pruned labeling component: CylinderSupport -/
namespace SensitivityCylinder
def DependsOn {ι β : Type*} (E : Finset (ι → β)) (C : Finset ι) : Prop :=
  ∀ a b : ι → β, (∀ i ∈ C, a i = b i) → (a ∈ E ↔ b ∈ E)
end SensitivityCylinder


/- Pruned labeling component: CylinderParametric -/
/-! The coordinate-split cylinder count with all equality instances explicit.
This avoids implicit equality choices when applying the theorem to function spaces. -/
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
namespace SensitivityCylinderParametric
noncomputable section
open SensitivityCylinder

/-- Exact uniform-counting independence for complementary coordinate supports. -/
theorem card_inter_mul_univ {ι β : Type*} [Fintype ι] [Fintype β] [Inhabited β]
    [DecidableEq ι] [DecidableEq β] [DecidableEq (ι → β)]
    (C : Finset ι) (E F : Finset (ι → β))
    (hE : DependsOn E C) (hF : DependsOn F Cᶜ) :
    (E ∩ F).card * Fintype.card (ι → β) = E.card * F.card := by
  let L := {i : ι // i ∈ C} → β
  let R := {i : ι // i ∉ C} → β
  let e : (ι → β) ≃ L × R :=
    Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ C) (fun _ => β)
  let zL : L := fun _ => default
  let zR : R := fun _ => default
  let A : Finset L := Finset.univ.filter fun l => e.symm (l,zR) ∈ E
  let B : Finset R := Finset.univ.filter fun r => e.symm (zL,r) ∈ F
  have hEP (f : ι → β) : f ∈ E ↔ (e f).1 ∈ A := by
    have hh := hE f (e.symm ((e f).1,zR)) (by
      intro i hi
      change f i = (if h : i ∈ C then f i else zR ⟨i,h⟩)
      rw [dif_pos hi])
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  have hFQ (f : ι → β) : f ∈ F ↔ (e f).2 ∈ B := by
    have hh := hF f (e.symm (zL,(e f).2)) (by
      intro i hi
      have hn : i ∉ C := Finset.mem_compl.mp hi
      change f i = (if h : i ∈ C then zL ⟨i,h⟩ else f i)
      rw [dif_neg hn])
    simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  have hcard (D : Finset (ι → β)) (A : Finset L) (B : Finset R)
      (h : ∀ f, f ∈ D ↔ e f ∈ A.product B) : D.card = A.card*B.card := by
    let eD : {f // f ∈ D} ≃ {z // z ∈ A.product B} := e.subtypeEquiv h
    simpa only [Fintype.card_coe, Finset.product_eq_sprod, Finset.card_product] using Fintype.card_congr eD
  have hcardE : E.card = A.card*Fintype.card R := by
    simpa only [Finset.card_univ] using hcard E A Finset.univ (by
      intro f
      simpa only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, and_true] using hEP f)
  have hcardF : F.card = Fintype.card L*B.card := by
    simpa only [Finset.card_univ] using hcard F Finset.univ B (by
      intro f
      simpa only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, true_and] using hFQ f)
  have hcardEF : (E ∩ F).card = A.card*B.card := by
    apply hcard
    intro f
    simp only [Finset.mem_inter, Finset.product_eq_sprod, Finset.mem_product, hEP, hFQ]
  have hcardAll : Fintype.card (ι → β) = Fintype.card L*Fintype.card R := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  rw [hcardEF, hcardE, hcardF, hcardAll]
  ring

/-- The rational form expected by a finite counting local lemma. -/
theorem bound_inter_card {ι β : Type*} [Fintype ι] [Fintype β] [Inhabited β]
    [DecidableEq ι] [DecidableEq β] [DecidableEq (ι → β)]
    (C : Finset ι) (E F : Finset (ι → β)) (p : ℚ)
    (hE : DependsOn E C) (hF : DependsOn F Cᶜ)
    (hp : (E.card : ℚ) ≤ p * Fintype.card (ι → β)) :
    ((E ∩ F).card : ℚ) ≤ p * (F.card : ℚ) := by
  have hN : (0 : ℚ) < Fintype.card (ι → β) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨fun _ => default⟩
  have heq : ((E ∩ F).card : ℚ) * Fintype.card (ι → β) =
      (E.card : ℚ) * (F.card : ℚ) := by
    exact_mod_cast card_inter_mul_univ C E F hE hF
  apply (mul_le_mul_iff_left₀ hN).mp
  calc
    ((E ∩ F).card : ℚ) * Fintype.card (ι → β) =
        (E.card : ℚ) * (F.card : ℚ) := heq
    _ ≤ (p * Fintype.card (ι → β)) * (F.card : ℚ) :=
      mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)
    _ = (p * (F.card : ℚ)) * Fintype.card (ι → β) := by ring

end
end SensitivityCylinderParametric

/- Pruned labeling component: FiniteLLL -/
/-! A finite asymmetric local lemma proved using unnormalized rational counts.
There are no conditional measures or divisions in the induction. The only
dependency hypothesis is the explicit loss bound supplied by cylinder counting.
This source is prepared without a kernel check while the main proof imports run.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators

namespace SensitivityLLL

variable {ι : Type*} [DecidableEq ι]

/-- Telescope one-step multiplicative bounds while adjoining a finite set. -/
theorem product_step_bound (Z : Finset ι → ℚ) (w : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i) (B A : Finset ι)
    (hstep : ∀ T ⊆ A, ∀ i ∈ A, i ∉ T →
      w i*Z (B ∪ T) ≤ Z (B ∪ insert i T)) :
    (∏ i ∈ A, w i)*Z B ≤ Z (B ∪ A) := by
  revert hstep
  induction A using Finset.induction_on with
  | empty => intro _; simp
  | @insert a A ha ih =>
    intro hstep
    have hchain : (∏ i ∈ A, w i)*Z B ≤ Z (B ∪ A) := by
      apply ih
      intro T hT i hi hnot
      exact hstep T (hT.trans (Finset.subset_insert _ _)) i
        (Finset.mem_insert_of_mem hi) hnot
    have hlast := hstep A (Finset.subset_insert _ _) a (Finset.mem_insert_self _ _) ha
    calc
      (∏ i ∈ insert a A, w i)*Z B = w a*((∏ i ∈ A, w i)*Z B) := by
        rw [Finset.prod_insert ha]
        ring
      _ ≤ w a*Z (B ∪ A) := mul_le_mul_of_nonneg_left hchain (hw a)
      _ ≤ Z (B ∪ insert a A) := hlast

/-- The inductive heart of the asymmetric finite local lemma. Neighborhoods
may include the event itself, which is convenient for upper dependency counts.
-/
theorem one_step_bound (Z : Finset ι → ℚ) (p x : ι → ℚ) (N : ι → Finset ι)
    (hZ : ∀ S, 0 ≤ Z S) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i ≤ x i*(∏ j ∈ N i, (1-x j)))
    (hLoss : ∀ S i, i ∉ S → Z S-Z (insert i S) ≤ p i*Z (S \ N i)) :
    ∀ S i, i ∉ S → (1-x i)*Z S ≤ Z (insert i S) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro i hi
    let A := S ∩ N i
    let B := S \ N i
    have hBA : B ∪ A = S := Finset.sdiff_union_inter S (N i)
    have hw0 (j : ι) : 0 ≤ 1-x j := sub_nonneg.mpr (le_of_lt (hx1 j))
    have hchain : (∏ j ∈ A, (1-x j))*Z B ≤ Z S := by
      have hh := product_step_bound Z (fun j => 1-x j) hw0 B A (by
        intro T hT j hj hnot
        have hjS : j ∈ S := (Finset.mem_inter.mp hj).1
        have hjN : j ∈ N i := (Finset.mem_inter.mp hj).2
        have hnotB : j ∉ B := fun h => (Finset.mem_sdiff.mp h).2 hjN
        have hnotBT : j ∉ B ∪ T := by
          intro h
          exact (Finset.mem_union.mp h).elim hnotB hnot
        have hsub : B ∪ T ⊆ S := by
          apply Finset.union_subset
          · exact Finset.sdiff_subset
          · exact hT.trans Finset.inter_subset_left
        have hproper : B ∪ T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
          intro heq
          exact hnotBT (heq.symm ▸ hjS)⟩
        have hlocal := ih (B ∪ T) hproper j hnotBT
        simpa only [Finset.union_insert] using hlocal)
      simpa only [hBA] using hh
    have hprod : (∏ j ∈ N i, (1-x j)) ≤ ∏ j ∈ A, (1-x j) := by
      apply Finset.prod_le_prod_of_subset_of_le_one Finset.inter_subset_right
      · intro j _
        exact hw0 j
      · intro j _ _
        linarith [hx0 j]
    have hPi : p i ≤ x i*(∏ j ∈ A, (1-x j)) :=
      (hp i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
    have hbad : p i*Z B ≤ x i*Z S := by
      calc
        _ ≤ (x i*(∏ j ∈ A, (1-x j)))*Z B :=
          mul_le_mul_of_nonneg_right hPi (hZ B)
        _ = x i*((∏ j ∈ A, (1-x j))*Z B) := by ring
        _ ≤ x i*Z S := mul_le_mul_of_nonneg_left hchain (hx0 i)
    have hloss := hLoss S i hi
    change Z S-Z (insert i S) ≤ p i*Z B at hloss
    nlinarith

/-- Every finite collection has positive avoidance weight. -/
theorem positive_of_loss (Z : Finset ι → ℚ) (p x : ι → ℚ) (N : ι → Finset ι)
    (hZ : ∀ S, 0 ≤ Z S) (hEmpty : 0 < Z ∅)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i ≤ x i*(∏ j ∈ N i, (1-x j)))
    (hLoss : ∀ S i, i ∉ S → Z S-Z (insert i S) ≤ p i*Z (S \ N i)) :
    ∀ S, 0 < Z S := by
  intro S
  have hstep := one_step_bound Z p x N hZ hx0 hx1 hp hLoss
  have hchain : (∏ i ∈ S, (1-x i))*Z ∅ ≤ Z S := by
    have hh := product_step_bound Z (fun i => 1-x i)
      (fun i => sub_nonneg.mpr (le_of_lt (hx1 i))) ∅ S (by
        intro T _ i _ hnot
        simpa only [Finset.empty_union] using hstep T i hnot)
    simpa only [Finset.empty_union] using hh
  have hprod : 0 < ∏ i ∈ S, (1-x i) :=
    Finset.prod_pos (fun i _ => sub_pos.mpr (hx1 i))
  exact (mul_pos hprod hEmpty).trans_le hchain

noncomputable section
open scoped Classical

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def avoid (bad : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  Finset.univ.filter fun ω => ∀ i ∈ S, ω ∉ bad i

theorem mem_avoid (bad : ι → Finset Ω) (S : Finset ι) (ω : Ω) :
    ω ∈ avoid bad S ↔ ∀ i ∈ S, ω ∉ bad i := by
  simp only [avoid,Finset.mem_filter,Finset.mem_univ,true_and]

theorem avoid_empty (bad : ι → Finset Ω) : avoid bad ∅ = Finset.univ := by
  ext ω
  simp [avoid]

theorem avoid_insert (bad : ι → Finset Ω) (S : Finset ι) (i : ι) :
    avoid bad (insert i S) = avoid bad S \ bad i := by
  ext ω
  simp [avoid,and_comm,and_left_comm,and_assoc]

theorem avoid_antitone (bad : ι → Finset Ω) {S T : Finset ι} (hST : S ⊆ T) :
    avoid bad T ⊆ avoid bad S := by
  intro ω hω
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro i hi
  exact (Finset.mem_filter.mp hω).2 i (hST hi)

/-- An explicit nonneighbor counting hypothesis implies the loss inequality.
This is the exact interface supplied by uniform cylinder independence. -/
theorem loss_of_nonneighbor_count (bad : ι → Finset Ω) (p : ι → ℚ)
    (N : ι → Finset ι)
    (hAway : ∀ i S, i ∉ S → (∀ j ∈ S, j ∉ N i) →
      ((bad i ∩ avoid bad S).card : ℚ) ≤ p i*((avoid bad S).card : ℚ)) :
    ∀ S i, i ∉ S →
      ((avoid bad S).card : ℚ)-((avoid bad (insert i S)).card : ℚ) ≤
        p i*((avoid bad (S \ N i)).card : ℚ) := by
  intro S i hi
  have hNat := Finset.card_sdiff_add_card_inter (avoid bad S) (bad i)
  have hRat : (((avoid bad S \ bad i).card : ℚ)) +
      (((avoid bad S ∩ bad i).card : ℚ)) = ((avoid bad S).card : ℚ) := by
    exact_mod_cast hNat
  have hLossEq : ((avoid bad S).card : ℚ)-((avoid bad (insert i S)).card : ℚ) =
      ((bad i ∩ avoid bad S).card : ℚ) := by
    rw [Finset.inter_comm] at hRat
    rw [avoid_insert]
    linarith
  rw [hLossEq]
  have hsub : bad i ∩ avoid bad S ⊆ bad i ∩ avoid bad (S \ N i) := by
    intro ω hω
    obtain ⟨hbad,hgood⟩ := Finset.mem_inter.mp hω
    exact Finset.mem_inter.mpr ⟨hbad,avoid_antitone bad Finset.sdiff_subset hgood⟩
  have hCard : ((bad i ∩ avoid bad S).card : ℚ) ≤
      ((bad i ∩ avoid bad (S \ N i)).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  apply hCard.trans
  apply hAway i (S \ N i)
  · exact fun h => hi (Finset.mem_sdiff.mp h).1
  · intro j hj
    exact (Finset.mem_sdiff.mp hj).2

/-- Finite asymmetric Lovasz local lemma with a fully explicit rational
nonneighbor-count hypothesis. It produces one point avoiding every bad event.
-/
theorem asymmetric_local_lemma [Fintype ι] [Nonempty Ω]
    (bad : ι → Finset Ω) (p x : ι → ℚ) (N : ι → Finset ι)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i ≤ x i*(∏ j ∈ N i, (1-x j)))
    (hAway : ∀ i S, i ∉ S → (∀ j ∈ S, j ∉ N i) →
      ((bad i ∩ avoid bad S).card : ℚ) ≤ p i*((avoid bad S).card : ℚ)) :
    ∃ ω, ∀ i, ω ∉ bad i := by
  let Z : Finset ι → ℚ := fun S => ((avoid bad S).card : ℚ)
  have hZ : ∀ S, 0 ≤ Z S := fun S => Nat.cast_nonneg _
  have hEmpty : 0 < Z ∅ := by
    have hΩ : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr inferInstance
    have hh : (0 : ℚ) < (Fintype.card Ω : ℚ) := by exact_mod_cast hΩ
    simpa only [Z,avoid_empty,Finset.card_univ] using hh
  have hpositive := positive_of_loss Z p x N hZ hEmpty hx0 hx1 hp
    (loss_of_nonneighbor_count bad p N hAway)
  have hNat : 0 < (avoid bad Finset.univ).card := by
    have hh : (0 : ℚ) < ((avoid bad Finset.univ).card : ℚ) := hpositive Finset.univ
    exact_mod_cast hh
  obtain ⟨ω,hω⟩ := Finset.card_pos.mp hNat
  refine ⟨ω,?_⟩
  intro i
  exact (mem_avoid bad Finset.univ ω).mp hω i (Finset.mem_univ _)

end
end SensitivityLLL

/- Pruned labeling component: GenericQLocality -/
/-!
Actual small-defect events and their dependency graph. An event is indexed by
a tolerance and a vertex subset; encoding tags are used only to bound its size.
-/
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205
open scoped Classical BigOperators

namespace SensitivityQLLL
noncomputable section
open SensitivityCylinder

/-- An outside-support interface avoids comparing concrete complement instances. -/
theorem bound_inter_card_outside {ι β : Type*} [Fintype ι] [Fintype β] [Inhabited β]
    [DecidableEq ι] [DecidableEq β] [DecidableEq (ι → β)]
    (C : Finset ι) (E F : Finset (ι → β)) (p : ℚ)
    (hE : DependsOn E C)
    (hF : ∀ a b : ι → β, (∀ i, i ∉ C → a i = b i) → (a ∈ F ↔ b ∈ F))
    (hp : (E.card : ℚ) ≤ p * Fintype.card (ι → β)) :
    ((E ∩ F).card : ℚ) ≤ p * (F.card : ℚ) := by
  apply SensitivityCylinderParametric.bound_inter_card C E F p hE
  · intro a b hab
    apply hF a b
    intro i hi
    exact hab i (Finset.mem_compl.mpr hi)
  · exact hp

local instance (priority := 2000) coordinateDecidableEq (k : ℕ) :
    DecidableEq (Fin k × Fin k) := Classical.decEq _

abbrev EdgeAssignment (k : ℕ) := (Fin k × Fin k) → Fin 2

local instance edgeAssignmentDecidableEq (k : ℕ) : DecidableEq (EdgeAssignment k) :=
  Classical.decEq _

/-- A genuine bad event, with no encoding choices in the event index. -/
def localBad {k : ℕ} (T : Tournament k) (q : ℕ) (I : Finset (Fin k)) :
    Finset (EdgeAssignment k) :=
  Finset.univ.filter fun a => ∃ m : Fin k → Fin 2,
    ∀ i ∈ I, (I.filter fun j => T.Adj i j ∧ a (i,j) ≠ m j).card ≤ q

theorem localBad_depends {k : ℕ} (T : Tournament k) (q : ℕ) (I : Finset (Fin k)) :
    DependsOn (localBad T q I) (T.internalEdges I) := by
  intro a b hab
  have hfilters (m : Fin k → Fin 2) (i : Fin k) (hi : i ∈ I) :
      (I.filter fun j => T.Adj i j ∧ a (i,j) ≠ m j) =
      (I.filter fun j => T.Adj i j ∧ b (i,j) ≠ m j) := by
    apply Finset.filter_congr
    intro j hj
    by_cases hij : T.Adj i j
    · have hp : (i,j) ∈ T.internalEdges I := by
        simp only [Tournament.internalEdges, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hi,hj⟩,hij⟩
      rw [hab (i,j) hp]
    · simp only [hij, false_and]
  simp only [localBad, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨m,hm⟩
    refine ⟨m,?_⟩
    intro i hi
    rw [← hfilters m i hi]
    exact hm i hi
  · rintro ⟨m,hm⟩
    refine ⟨m,?_⟩
    intro i hi
    rw [hfilters m i hi]
    exact hm i hi

/-- The already verified q-tag encoder bounds a single actual subset event. -/
theorem localBad_card_le {k : ℕ} (T : Tournament k) (q : ℕ) (I : Finset (Fin k)) :
    (localBad T q I).card ≤
      2^I.card * (I.card^(q*I.card) * 2^(k*k-I.card.choose 2)) := by
  let encoded : Finset (Fin k → Fin k → Fin 2) :=
    (Finset.univ : Finset (I → Fin 2)).biUnion fun m =>
      (Finset.univ : Finset (I → Fin q → I)).biUnion fun e => SensitivityQ.good T I m e
  have hc : (localBad T q I).card ≤ encoded.card := by
    apply Finset.card_le_card_of_injOn (fun a : EdgeAssignment k => fun i j => a (i,j))
    · intro a ha
      obtain ⟨m,hm⟩ := (Finset.mem_filter.mp ha).2
      obtain ⟨e,he⟩ := SensitivityQ.exists_encoder T I (fun i j => a (i,j)) m hm
      exact Finset.mem_biUnion.mpr ⟨fun j => m j.1, Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,he⟩⟩
    · intro a ha b hb hab
      funext ij
      exact congrFun (congrFun hab ij.1) ij.2
  apply hc.trans
  apply Finset.card_biUnion_le.trans
  have hm (m : I → Fin 2) :
      ((Finset.univ : Finset (I → Fin q → I)).biUnion fun e =>
        SensitivityQ.good T I m e).card ≤
        I.card^(q*I.card)*2^(k*k-I.card.choose 2) := by
    apply Finset.card_biUnion_le.trans
    apply (Finset.sum_le_sum fun e _ => SensitivityQ.good_card_le T I m e).trans
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, ← pow_mul]
  apply (Finset.sum_le_sum fun m _ => hm m).trans
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun,
    Fintype.card_coe, Fintype.card_fin]

def eventProbability (q s : ℕ) : ℚ :=
  ((2^s*s^(q*s) : ℕ) : ℚ) / ((2^(s.choose 2) : ℕ) : ℚ)

theorem localBad_probability_bound {k : ℕ} (T : Tournament k)
    (q : ℕ) (I : Finset (Fin k)) :
    ((localBad T q I).card : ℚ) ≤
      eventProbability q I.card * Fintype.card (EdgeAssignment k) := by
  have hroom : I.card.choose 2 ≤ k*k := by
    rw [← T.card_internalEdges I]
    simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (T.internalEdges I))
  have hpow : (2 : ℚ)^(I.card.choose 2) * 2^(k*k-I.card.choose 2) = 2^(k*k) := by
    rw [← pow_add, Nat.add_sub_cancel' hroom]
  have hden : (2 : ℚ)^(I.card.choose 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    ((localBad T q I).card : ℚ) ≤
        (2 : ℚ)^I.card * ((I.card : ℚ)^(q*I.card) * 2^(k*k-I.card.choose 2)) := by
      exact_mod_cast localBad_card_le T q I
    _ = eventProbability q I.card * Fintype.card (EdgeAssignment k) := by
      simp only [eventProbability, EdgeAssignment, Fintype.card_fun,
        Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
      rw [← hpow]
      ring

/-- Two vertex sets sharing at most one vertex use disjoint arc coordinates. -/
theorem internalEdges_disjoint {k : ℕ} (T : Tournament k) (I J : Finset (Fin k))
    (hIJ : (I ∩ J).card ≤ 1) : Disjoint (T.internalEdges I) (T.internalEdges J) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i,j⟩ hi hj
  obtain ⟨⟨hiI,hjI⟩,hij⟩ : (i ∈ I ∧ j ∈ I) ∧ T.Adj i j := by
    simpa only [Tournament.internalEdges, Finset.mem_filter, Finset.mem_product] using hi
  obtain ⟨⟨hiJ,hjJ⟩,_⟩ : (i ∈ J ∧ j ∈ J) ∧ T.Adj i j := by
    simpa only [Tournament.internalEdges, Finset.mem_filter, Finset.mem_product] using hj
  have hh : 1 < (I ∩ J).card := Finset.one_lt_card.mpr
    ⟨i,Finset.mem_inter.mpr ⟨hiI,hiJ⟩,
      j,Finset.mem_inter.mpr ⟨hjI,hjJ⟩,T.ne_of_adj hij⟩
  omega

/-- One index per tolerance/subset pair, independently of all encoder choices. -/
def EventIndex (k Q : ℕ) (s : Fin (Q+1) → ℕ) :=
  Σ q : Fin (Q+1), Finset.powersetCard (s q) (Finset.univ : Finset (Fin k))

instance eventIndexFinite (k Q : ℕ) (s : Fin (Q+1) → ℕ) : Finite (EventIndex k Q s) := by
  unfold EventIndex
  infer_instance

noncomputable instance eventIndexFintype (k Q : ℕ) (s : Fin (Q+1) → ℕ) :
    Fintype (EventIndex k Q s) := Fintype.ofFinite _

noncomputable instance eventIndexDecidableEq (k Q : ℕ) (s : Fin (Q+1) → ℕ) :
    DecidableEq (EventIndex k Q s) := Classical.decEq _
















end
end SensitivityQLLL

/- Pruned labeling component: OverlapDegree -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

open scoped BigOperators

namespace SensitivityLLL
noncomputable section

/-- Every b-subset meeting A in at least two points contains some pair of A.
Covering by those pairs counts each possible dependent subset at least once.
The count includes A itself when it has size b, which is safe for loop-free
LLL dependency graphs as well. -/
theorem card_overlap_two_le_pairCount {α : Type*} [DecidableEq α]
    (U A : Finset α) (hAU : A ⊆ U) (b : ℕ) (hb : 2 ≤ b) :
    ((U.powersetCard b).filter fun B => 2 ≤ (A ∩ B).card).card ≤
      A.card.choose 2 * (U.card - 2).choose (b - 2) := by
  classical
  let cover := (A.powersetCard 2).biUnion fun C =>
    (U.powersetCard b).filter fun B => C ⊆ B
  have hsub : ((U.powersetCard b).filter fun B => 2 ≤ (A ∩ B).card) ⊆ cover := by
    intro B hB
    obtain ⟨hBU, hAB⟩ := Finset.mem_filter.mp hB
    obtain ⟨C, hC, hCcard⟩ := Finset.exists_subset_card_eq hAB
    apply Finset.mem_biUnion.mpr
    refine ⟨C, Finset.mem_powersetCard.mpr ⟨hC.trans Finset.inter_subset_left, hCcard⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hBU, hC.trans Finset.inter_subset_right⟩
  have hcount (C : Finset α) (hC : C ∈ A.powersetCard 2) :
      ((U.powersetCard b).filter fun B => C ⊆ B).card =
        (U.card - 2).choose (b - 2) := by
    obtain ⟨hCA, hCcard⟩ := Finset.mem_powersetCard.mp hC
    rw [Finset.card_filter_powersetCard_subset C U b (hCA.trans hAU) (by omega), hCcard]
  calc
    ((U.powersetCard b).filter fun B => 2 ≤ (A ∩ B).card).card ≤ cover.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ C ∈ A.powersetCard 2,
        ((U.powersetCard b).filter fun B => C ⊆ B).card := Finset.card_biUnion_le
    _ = ∑ _C ∈ A.powersetCard 2, (U.card - 2).choose (b - 2) :=
      Finset.sum_congr rfl hcount
    _ = A.card.choose 2 * (U.card - 2).choose (b - 2) := by simp

/-- The finite-vertex specialization used by the event index. -/
theorem card_overlap_two_fin_le (k : ℕ) (A : Finset (Fin k))
    (b : ℕ) (hb : 2 ≤ b) :
    (((Finset.univ : Finset (Fin k)).powersetCard b).filter
      fun B => 2 ≤ (A ∩ B).card).card ≤
      A.card.choose 2 * (k - 2).choose (b - 2) := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    card_overlap_two_le_pairCount (Finset.univ : Finset (Fin k)) A
      (Finset.subset_univ A) b hb







end
end SensitivityLLL

/- Pruned labeling component: TypedActivity -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

open scoped BigOperators

namespace SensitivityLLL
noncomputable section

/-- A typewise upper bound on neighbor counts gives a typewise lower bound
on the asymmetric LLL product, because all factors lie in [0,1]. -/
theorem prod_by_type_lower {E Q : Type*} [DecidableEq E] [Fintype Q] [DecidableEq Q]
    (N : Finset E) (kind : E → Q) (x : Q → ℚ) (C : Q → ℕ) (a : ℕ)
    (hx0 : ∀ q, 0 ≤ x q) (hx1 : ∀ q, x q ≤ 1)
    (hcount : ∀ q, (N.filter fun j => kind j = q).card ≤ a * C q) :
    (∏ q, (1 - x q) ^ C q) ^ a ≤ ∏ j ∈ N, (1 - x (kind j)) := by
  classical
  calc
    (∏ q, (1 - x q) ^ C q) ^ a = ∏ q, (1 - x q) ^ (a * C q) := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro q _
      rw [← pow_mul, Nat.mul_comm]
    _ ≤ ∏ q, (1 - x q) ^ (N.filter fun j => kind j = q).card := by
      apply Finset.prod_le_prod
      · intro q _
        exact pow_nonneg (by linarith [hx1 q]) _
      · intro q _
        exact pow_le_pow_of_le_one (by linarith [hx1 q])
          (by linarith [hx0 q]) (hcount q)
    _ = ∏ j ∈ N, (1 - x (kind j)) := by
      simpa using Finset.prod_fiberwise' N kind (fun q => 1 - x q)

/-- Finite weighted Bernoulli inequality, with no enumeration of individual
neighbors and no closed powers of the total sample-space cardinality. -/
theorem weighted_bernoulli_finset {Q : Type*} [DecidableEq Q]
    (S : Finset Q) (x : Q → ℚ) (C : Q → ℕ)
    (hx0 : ∀ q, 0 ≤ x q) (hx1 : ∀ q, x q ≤ 1) :
    1 - ∑ q ∈ S, (C q : ℚ) * x q ≤ ∏ q ∈ S, (1 - x q) ^ C q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
    rw [Finset.sum_insert hq, Finset.prod_insert hq]
    have hf0 : (0 : ℚ) ≤ (1 - x q) ^ C q :=
      pow_nonneg (by linarith [hx1 q]) _
    have hf1 : (1 - x q) ^ C q ≤ (1 : ℚ) :=
      pow_le_one₀ (by linarith [hx1 q]) (by linarith [hx0 q])
    have hB : 1 - (C q : ℚ) * x q ≤ (1 - x q) ^ C q := by
      simpa only [mul_neg, sub_eq_add_neg] using
        (one_add_mul_le_pow (R := ℚ) (a := -x q) (by linarith [hx1 q]) (C q))
    have hsum0 : (0 : ℚ) ≤ ∑ j ∈ S, (C j : ℚ) * x j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hx0 j)
    have hmul := mul_le_mul_of_nonneg_left ih hf0
    nlinarith [mul_nonneg (sub_nonneg.mpr hf1) hsum0]

/-- One rational gamma certificate gives all LLL neighbor-product lower bounds
when the degree matrix has the rank-one form a*C(q). -/
theorem prod_by_type_lower_gamma {E Q : Type*} [DecidableEq E]
    [Fintype Q] [DecidableEq Q]
    (N : Finset E) (kind : E → Q) (x : Q → ℚ) (C : Q → ℕ)
    (a : ℕ) (γ : ℚ) (hγ : 1 < γ)
    (hx0 : ∀ q, 0 ≤ x q) (hx1 : ∀ q, x q ≤ 1)
    (hcount : ∀ q, (N.filter fun j => kind j = q).card ≤ a * C q)
    (hbudget : ∑ q, (C q : ℚ) * x q ≤ 1 - 1 / γ) :
    (1 / γ) ^ a ≤ ∏ j ∈ N, (1 - x (kind j)) := by
  have hbase : (1 / γ : ℚ) ≤ ∏ q, (1 - x q) ^ C q := by
    have hB := weighted_bernoulli_finset Finset.univ x C hx0 hx1
    linarith
  exact (pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 1 / γ) hbase a).trans
    (prod_by_type_lower N kind x C a hx0 hx1 hcount)

/-- Positive integer weights turn the same budget into strict activity bounds. -/
theorem activity_lt_one_of_budget {Q : Type*} [Fintype Q] [DecidableEq Q]
    (x : Q → ℚ) (C : Q → ℕ) (γ : ℚ) (hγ : 1 < γ)
    (hx0 : ∀ q, 0 ≤ x q) (hC : ∀ q, 1 ≤ C q)
    (hbudget : ∑ q, (C q : ℚ) * x q ≤ 1 - 1 / γ) :
    ∀ q, x q < 1 := by
  intro q
  have hterm : (C q : ℚ) * x q ≤ ∑ j, (C j : ℚ) * x j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hx0 j))
      (Finset.mem_univ q)
  have hCq : (1 : ℚ) ≤ C q := by exact_mod_cast hC q
  have hxC : x q ≤ (C q : ℚ) * x q := by nlinarith [hx0 q]
  have hinv : (0 : ℚ) < 1 / γ := one_div_pos.mpr (by linarith)
  linarith

/-- Final rank-one activity criterion. The actual activity of an event of type
q is p(q)*gamma^u(q). One budget gives every event's asymmetric LLL inequality. -/
theorem rank_one_activity_condition {E Q : Type*} [DecidableEq E]
    [Fintype Q] [DecidableEq Q]
    (N : Finset E) (kind : E → Q) (p : Q → ℚ) (u C : Q → ℕ)
    (q₀ : Q) (γ : ℚ) (hγ : 1 < γ) (hp0 : ∀ q, 0 ≤ p q)
    (hx1 : ∀ q, p q * γ ^ u q < 1)
    (hcount : ∀ q, (N.filter fun j => kind j = q).card ≤ u q₀ * C q)
    (hbudget : ∑ q, (C q : ℚ) * (p q * γ ^ u q) ≤ 1 - 1 / γ) :
    p q₀ ≤ (p q₀ * γ ^ u q₀) *
      ∏ j ∈ N, (1 - p (kind j) * γ ^ u (kind j)) := by
  have hγ0 : (0 : ℚ) < γ := by linarith
  have hx0 (q : Q) : (0 : ℚ) ≤ p q * γ ^ u q :=
    mul_nonneg (hp0 q) (pow_nonneg hγ0.le _)
  have hprod := prod_by_type_lower_gamma N kind (fun q => p q * γ ^ u q) C
    (u q₀) γ hγ hx0 (fun q => (hx1 q).le) hcount hbudget
  have hcancel : (p q₀ * γ ^ u q₀) * (1 / γ) ^ u q₀ = p q₀ := by
    rw [mul_assoc, ← mul_pow]
    simp [one_div, ne_of_gt hγ0]
  calc
    p q₀ = (p q₀ * γ ^ u q₀) * (1 / γ) ^ u q₀ := hcancel.symm
    _ ≤ (p q₀ * γ ^ u q₀) *
        ∏ j ∈ N, (1 - p (kind j) * γ ^ u (kind j)) :=
      mul_le_mul_of_nonneg_left hprod (hx0 q₀)

end
end SensitivityLLL

/- Pruned labeling component: GammaBudget -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
open scoped BigOperators

namespace SensitivityLLL

/-- Clear a common power denominator in a finite family of rational
activities. The final hypothesis is a single natural-number inequality. -/
theorem rational_power_budget {Q : Type*} [Fintype Q]
    (C tags u : Q → ℕ) (U a d n : ℕ)
    (hd : 0 < d) (hn : 0 < n) (hu : ∀ q, u q ≤ U)
    (hcert : n * (∑ q, C q * tags q * a ^ u q * d ^ (U-u q)) ≤
      (n-d) * d ^ U) (hdn : d ≤ n) :
    ∑ q, (C q : ℚ) * ((tags q : ℚ) * ((a : ℚ) / d) ^ u q) ≤
      1 - (d : ℚ) / n := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hn0 : (0 : ℚ) < n := by exact_mod_cast hn
  have hden : (0 : ℚ) < (d : ℚ) ^ U := pow_pos (by exact_mod_cast hd) _
  have hterm (q : Q) :
      (C q : ℚ) * ((tags q : ℚ) * ((a : ℚ) / d) ^ u q) =
      ((C q * tags q * a ^ u q * d ^ (U-u q) : ℕ) : ℚ) / (d : ℚ) ^ U := by
    have hsplit : (d : ℚ) ^ U = (d : ℚ) ^ u q * (d : ℚ) ^ (U-u q) := by
      rw [← pow_add, Nat.add_sub_of_le (hu q)]
    apply (eq_div_iff (ne_of_gt hden)).mpr
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [div_pow, hsplit]
    field_simp [hd0]
    <;> ring
  have hsum :
      ∑ q, (C q : ℚ) * ((tags q : ℚ) * ((a : ℚ) / d) ^ u q) =
      ((∑ q, C q * tags q * a ^ u q * d ^ (U-u q) : ℕ) : ℚ) / (d : ℚ) ^ U := by
    simp_rw [hterm]
    rw [← Finset.sum_div, Nat.cast_sum]
  rw [hsum]
  apply (div_le_iff₀ hden).mpr
  have hcertQ : (n : ℚ) *
      ((∑ q, C q * tags q * a ^ u q * d ^ (U-u q) : ℕ) : ℚ) ≤
      ((n : ℚ) - d) * (d : ℚ) ^ U := by
    have hh : (n : ℚ) *
        ((∑ q, C q * tags q * a ^ u q * d ^ (U-u q) : ℕ) : ℚ) ≤
        ((n-d : ℕ) : ℚ) * (d : ℚ) ^ U := by exact_mod_cast hcert
    simpa only [Nat.cast_sub hdn] using hh
  have hmul : (1 - (d : ℚ) / n) * (d : ℚ) ^ U * n =
      ((n : ℚ) - d) * (d : ℚ) ^ U := by
    field_simp [ne_of_gt hn0]
    <;> ring
  apply (mul_le_mul_iff_right₀ hn0).mp
  calc
    (n : ℚ) * ((∑ q, C q * tags q * a ^ u q * d ^ (U-u q) : ℕ) : ℚ) ≤
        ((n : ℚ) - d) * (d : ℚ) ^ U := hcertQ
    _ = (n : ℚ) * ((1 - (d : ℚ) / n) * (d : ℚ) ^ U) := by
      rw [← hmul]
      ring

end SensitivityLLL


end SensitivityLabelCache12607
end



/- Component: RowTournamentCountPrunedFast -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
open scoped Classical BigOperators

namespace SensitivityRowCounting
noncomputable section

open SensitivityLabelCache12607.OAI.Paper320
open SensitivityLabelCache12607.SensitivityQLLL
open SharperRowCounting SharperRowLLL

def rows {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) (i : I) :
    Finset (Fin k × Fin k) :=
  (I.filter (T.Adj i.val)).image (fun j => (i.val, j))

theorem rows_card {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) (i : I) :
    (rows T I i).card = (I.filter (T.Adj i.val)).card := by
  apply Finset.card_image_of_injective
  intro j j' h
  exact congrArg Prod.snd h

theorem rows_filter_card {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) (i : I)
    (P : (Fin k × Fin k) → Prop) [DecidablePred P] :
    ((rows T I i).filter P).card =
      (I.filter (fun j => T.Adj i.val j ∧ P (i.val, j))).card := by
  rw [rows, Finset.filter_image, Finset.card_image_of_injective]
  · rw [Finset.filter_filter]
  · intro j j' h
    exact congrArg Prod.snd h

theorem rows_union {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) :
    rowUnion (rows T I) = T.internalEdges I := by
  ext p
  simp only [rowUnion, Finset.mem_biUnion, Finset.mem_univ, true_and,
    rows, Finset.mem_image, Finset.mem_filter,
    Tournament.internalEdges, Finset.mem_product]
  constructor
  · rintro ⟨i, j, ⟨hj, hij⟩, hp⟩
    subst p
    exact ⟨⟨i.property, hj⟩, hij⟩
  · rintro ⟨⟨hi, hj⟩, hij⟩
    exact ⟨⟨p.1, hi⟩, p.2, ⟨hj, hij⟩, rfl⟩

theorem rows_card_lt {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) (i : I) :
    (rows T I i).card < I.card := by
  rw [rows_card]
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr
    ⟨i.val, i.property, T.loopless i.val⟩)

theorem rows_card_sum {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) :
    (∑ i : I, (rows T I i).card) = I.card.choose 2 := by
  simp_rw [rows_card]
  rw [Finset.sum_coe_sort (s := I)
    (f := fun i : Fin k => (I.filter (T.Adj i)).card), ← T.card_internalEdges I]
  simp only [Tournament.internalEdges, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

theorem row_product_bound (cfg : Fin 2) (q : Fin 5)
    {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) (hI : I.card = cutoff cfg q) :
    (∏ i : I, rowPatterns q.val (rows T I i).card) ≤ balancedProduct cfg q := by
  obtain ⟨_, _, hM, hN, hb, hE⟩ := elementary_bounds cfg q
  have hs : (∑ i : I, (rows T I i).card) =
      lowDegree cfg q * Fintype.card I + highCount cfg q := by
    rw [rows_card_sum, Fintype.card_coe, hI]
    simpa only [Nat.mul_comm] using hE.symm
  have ht (i : I) :
      rowPatterns q.val (rows T I i).card *
          lowValue cfg q ^ (rows T I i).card * highValue cfg q ^ lowDegree cfg q ≤
        lowValue cfg q ^ (lowDegree cfg q + 1) *
          highValue cfg q ^ (rows T I i).card := by
    have hi : (rows T I i).card < cutoff cfg q := by
      simpa only [hI] using rows_card_lt T I i
    exact tangent_certificates cfg q ⟨(rows T I i).card, hi⟩
  have hp := balanced_product_le (fun i : I => (rows T I i).card)
    (fun i : I => rowPatterns q.val (rows T I i).card)
    (lowDegree cfg q) (highCount cfg q) (lowValue cfg q) (highValue cfg q)
    (by simpa only [Fintype.card_coe, hI] using hb) hM hN hs ht
  simpa only [Fintype.card_coe, hI, balancedProduct] using hp

def extendedColor {k : ℕ} (I : Finset (Fin k)) (m : I → Fin 2)
    (e : Fin k × Fin k) : Fin 2 :=
  if h : e.2 ∈ I then m ⟨e.2, h⟩ else 0

theorem localBad_row_count (cfg : Fin 2) (q : Fin 5)
    {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) (hI : I.card = cutoff cfg q) :
    (localBad T q.val I).card ≤
      2 ^ I.card * (balancedProduct cfg q * 2 ^ (k*k - I.card.choose 2)) := by
  let encoded : Finset (EdgeAssignment k) :=
    (Finset.univ : Finset (I → Fin 2)).biUnion fun m =>
      rowGood (rows T I) (fun _ => q.val) (extendedColor I m)
  have hc : localBad T q.val I ⊆ encoded := by
    intro a ha
    obtain ⟨m, hm⟩ := (Finset.mem_filter.mp ha).2
    refine Finset.mem_biUnion.mpr ⟨(fun j => m j.val), Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    rw [rows_filter_card]
    convert hm i.val i.property using 1
    congr 1
    apply Finset.filter_congr
    intro j hj
    simp only [extendedColor, dif_pos hj]
  have hg (m : I → Fin 2) :
      (rowGood (rows T I) (fun _ => q.val) (extendedColor I m)).card ≤
        2 ^ (k*k - I.card.choose 2) * balancedProduct cfg q := by
    have h := rowGood_card_le (rows T I) (fun _ => q.val) (extendedColor I m)
    rw [rows_union, T.card_internalEdges] at h
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact h.trans (Nat.mul_le_mul_left _ (row_product_bound cfg q T I hI))
  apply (Finset.card_le_card hc).trans
  apply Finset.card_biUnion_le.trans
  calc
    (∑ m : I → Fin 2,
        (rowGood (rows T I) (fun _ => q.val) (extendedColor I m)).card) ≤
      ∑ _m : I → Fin 2, 2 ^ (k*k - I.card.choose 2) * balancedProduct cfg q :=
        Finset.sum_le_sum (fun m _ => hg m)
    _ = 2 ^ I.card * (balancedProduct cfg q * 2 ^ (k*k - I.card.choose 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_coe, Fintype.card_fin, smul_eq_mul]
      ring

def rowProbability (cfg : Fin 2) (q : Fin 5) : ℚ :=
  ((2 ^ cutoff cfg q * balancedProduct cfg q : ℕ) : ℚ) /
    ((2 ^ (cutoff cfg q).choose 2 : ℕ) : ℚ)

theorem localBad_row_probability (cfg : Fin 2) (q : Fin 5)
    {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) (hI : I.card = cutoff cfg q) :
    ((localBad T q.val I).card : ℚ) ≤
      rowProbability cfg q * Fintype.card (EdgeAssignment k) := by
  have hroom : I.card.choose 2 ≤ k*k := by
    rw [← T.card_internalEdges I]
    simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (T.internalEdges I))
  have hpow : (2 : ℚ) ^ (I.card.choose 2) * 2 ^ (k*k-I.card.choose 2) =
      2 ^ (k*k) := by
    rw [← pow_add, Nat.add_sub_cancel' hroom]
  have hden : (2 : ℚ) ^ (I.card.choose 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    ((localBad T q.val I).card : ℚ) ≤
        (2 : ℚ) ^ I.card *
          ((balancedProduct cfg q : ℚ) * 2 ^ (k*k-I.card.choose 2)) := by
      exact_mod_cast localBad_row_count cfg q T I hI
    _ = rowProbability cfg q * Fintype.card (EdgeAssignment k) := by
      simp only [rowProbability, EdgeAssignment, Fintype.card_fun,
        Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [← hI]
      field_simp
      rw [← hpow]
      ring




end
end SensitivityRowCounting
end



/- Component: SharperSharedLabelingPrunedFast -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 4096
open scoped Classical BigOperators

namespace SensitivityRowCounting
noncomputable section

open SensitivityLabelCache12607.OAI.Paper320
open SensitivityLabelCache12607.SensitivityQLLL
open SensitivityLabelCache12607.SensitivityCylinder
open SharperRowLLL







theorem activity_double (tag E a d : ℕ) (hd : 0 < d) :
    ((tag : ℚ) / ((2 ^ E : ℕ) : ℚ)) * (((2*a : ℕ) : ℚ) / d) ^ E =
      (tag : ℚ) * ((a : ℚ) / d) ^ E := by
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_pow, mul_pow, div_pow]
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp [hd0]
  <;> ring



















end
end SensitivityRowCounting
end



/- Component: Research.SourceCoherentCounting -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped Classical BigOperators

namespace SensitivitySourceLabeling
noncomputable section

open SensitivityLabelCache12607.OAI.Paper320
open SensitivityLabelCache12607.SensitivityQLLL

def outN {k : ℕ} (T : Tournament k) (v : Fin k) : Finset (Fin k) :=
  Finset.univ.filter (T.Adj v)

def inN {k : ℕ} (T : Tournament k) (v : Fin k) : Finset (Fin k) :=
  Finset.univ.filter (fun w => T.Adj w v)

def IsSource {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) (s : Fin k) : Prop :=
  s ∈ I ∧ ∀ j ∈ I, j ≠ s → T.Adj s j

def HasSource {k : ℕ} (T : Tournament k) (I : Finset (Fin k)) : Prop :=
  ∃ s, IsSource T I s

def sourceSets {k : ℕ} (T : Tournament k) (t : ℕ) : Finset (Finset (Fin k)) :=
  (Finset.univ.powersetCard t).filter (HasSource T)

def sourceWith {k : ℕ} (T : Tournament k) (t : ℕ) (s : Fin k)
    (B : Finset (Fin k)) : Finset (Finset (Fin k)) :=
  (Finset.univ.powersetCard t).filter (fun I => IsSource T I s ∧ B ⊆ I)

theorem head_ne_source {k : ℕ} (T : Tournament k) (I : Finset (Fin k))
    (s : Fin k) (hs : IsSource T I s) {i j : Fin k}
    (hi : i ∈ I) (hij : T.Adj i j) : j ≠ s := by
  rintro rfl
  exact T.not_adj_reverse hij (hs.2 i hi (T.ne_of_adj hij))

theorem erase_subset_out {k : ℕ} (T : Tournament k) (I : Finset (Fin k))
    (s : Fin k) (hs : IsSource T I s) : I.erase s ⊆ outN T s := by
  intro j hj
  obtain ⟨hjs, hj⟩ := Finset.mem_erase.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.2 j hj hjs⟩

theorem indegree_regular {k D : ℕ} (T : Tournament k) (hk : k = 2*D+1)
    (hout : ∀ v, (outN T v).card = D) (v : Fin k) : (inN T v).card = D := by
  have hd : Disjoint (inN T v) (outN T v) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    exact T.not_adj_reverse (Finset.mem_filter.mp hj).2
      (Finset.mem_filter.mp hj').2
  have hu : inN T v ∪ outN T v = Finset.univ.erase v := by
    ext j
    simp only [inN, outN, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · rintro (h | h)
      · exact T.ne_of_adj h
      · exact (T.ne_of_adj h).symm
    · exact T.adj_or_reverse
  have hc := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, hout] at hc
  omega

theorem card_sourceWith_le {k D t : ℕ} (T : Tournament k)
    (hout : ∀ v, (outN T v).card = D) (s : Fin k) (B : Finset (Fin k))
    (hsB : s ∉ B) (hB : B ⊆ outN T s) (ht : B.card + 1 ≤ t) :
    (sourceWith T t s B).card ≤ (D-B.card).choose (t-1-B.card) := by
  let target := ((outN T s).powersetCard (t-1)).filter (fun R => B ⊆ R)
  have hc : (sourceWith T t s B).card ≤ target.card := by
    apply Finset.card_le_card_of_injOn (fun I : Finset (Fin k) => I.erase s)
    · intro I hI
      obtain ⟨hsize, hsrc, hBI⟩ := Finset.mem_filter.mp hI
      have hcard : I.card = t := (Finset.mem_powersetCard.mp hsize).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨erase_subset_out T I s hsrc, ?_⟩, ?_⟩
      · rw [Finset.card_erase_of_mem hsrc.1, hcard]
      · intro b hb
        exact Finset.mem_erase.mpr ⟨(by rintro rfl; exact hsB hb), hBI hb⟩
    · intro I hI J hJ hEq
      have hsI : s ∈ I := (Finset.mem_filter.mp hI).2.1.1
      have hsJ : s ∈ J := (Finset.mem_filter.mp hJ).2.1.1
      have h := congrArg (fun R : Finset (Fin k) => insert s R) hEq
      simpa only [Finset.insert_erase hsI, Finset.insert_erase hsJ] using h
  apply hc.trans
  have hb : B.card ≤ t-1 := by omega
  dsimp only [target]
  rw [Finset.card_filter_powersetCard_subset B (outN T s) (t-1) hB hb,
    hout]

theorem source_star_card_le {k D t : ℕ} (T : Tournament k) (hk : k = 2*D+1)
    (hout : ∀ v, (outN T v).card = D) (ht : 3 ≤ t) (hroom : t-1 ≤ D)
    {a b : Fin k} (hab : T.Adj a b) :
    ((sourceSets T t).filter (fun I => a ∈ I ∧ b ∈ I)).card ≤
      (t-1) * (D-1).choose (t-2) := by
  have hne : a ≠ b := T.ne_of_adj hab
  let common := inN T a ∩ inN T b
  let cover := sourceWith T t a {b} ∪
    common.biUnion (fun s => sourceWith T t s {a,b})
  have hsub : (sourceSets T t).filter (fun I => a ∈ I ∧ b ∈ I) ⊆ cover := by
    intro I hI
    obtain ⟨hI, ha, hb⟩ := Finset.mem_filter.mp hI
    obtain ⟨hsize, s, hs⟩ := Finset.mem_filter.mp hI
    by_cases hsa : s = a
    · subst s
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hsize, hs, by simpa only [Finset.singleton_subset_iff] using hb⟩)
    · have hsb : s ≠ b := by
        rintro rfl
        exact T.not_adj_reverse hab (hs.2 a ha hne)
      have hca : T.Adj s a := hs.2 a ha (Ne.symm hsa)
      have hcb : T.Adj s b := hs.2 b hb (Ne.symm hsb)
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨s,
        Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcb⟩⟩,
        Finset.mem_filter.mpr ⟨hsize, hs, by
          simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
          exact ⟨ha,hb⟩⟩⟩
  have hcommon : common.card ≤ D-1 := by
    have hsub : common ⊆ (inN T b).erase a := by
      intro s hs
      obtain ⟨hsa, hsb⟩ := Finset.mem_inter.mp hs
      exact Finset.mem_erase.mpr
        ⟨T.ne_of_adj (Finset.mem_filter.mp hsa).2, hsb⟩
    have ha : a ∈ inN T b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
    simpa only [Finset.card_erase_of_mem ha, indegree_regular T hk hout b] using
      Finset.card_le_card hsub
  have hleft : (sourceWith T t a {b}).card ≤ (D-1).choose (t-2) := by
    have hB : ({b} : Finset (Fin k)) ⊆ outN T a := by
      simp only [Finset.singleton_subset_iff, outN, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hab
    simpa only [Finset.card_singleton, Nat.sub_sub] using
      card_sourceWith_le T hout a {b} (by simpa using hne) hB (by simp; omega)
  have hright (s : Fin k) (hs : s ∈ common) :
      (sourceWith T t s {a,b}).card ≤ (D-2).choose (t-3) := by
    obtain ⟨hsa, hsb⟩ := Finset.mem_inter.mp hs
    have hsa' : T.Adj s a := (Finset.mem_filter.mp hsa).2
    have hsb' : T.Adj s b := (Finset.mem_filter.mp hsb).2
    have hsB : s ∉ ({a,b} : Finset (Fin k)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or.mpr ⟨T.ne_of_adj hsa', T.ne_of_adj hsb'⟩
    have hB : ({a,b} : Finset (Fin k)) ⊆ outN T s := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsa'⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsb'⟩⟩
    simpa only [Finset.card_pair hne, Nat.sub_sub] using
      card_sourceWith_le T hout s {a,b} hsB hB (by simp only [Finset.card_pair hne]; omega)
  have hmul : (D-1) * (D-2).choose (t-3) =
      (D-1).choose (t-2) * (t-2) := by
    have h := Nat.add_one_mul_choose_eq (D-2) (t-3)
    have hd : D-2+1 = D-1 := by omega
    have ht' : t-3+1 = t-2 := by omega
    simpa only [hd, ht'] using h
  calc
    ((sourceSets T t).filter (fun I => a ∈ I ∧ b ∈ I)).card ≤ cover.card :=
      Finset.card_le_card hsub
    _ ≤ (sourceWith T t a {b}).card +
        (common.biUnion (fun s => sourceWith T t s {a,b})).card := Finset.card_union_le _ _
    _ ≤ (D-1).choose (t-2) + ∑ s ∈ common, (sourceWith T t s {a,b}).card :=
      Nat.add_le_add hleft Finset.card_biUnion_le
    _ ≤ (D-1).choose (t-2) + common.card * (D-2).choose (t-3) := by
      apply Nat.add_le_add_left
      simpa only [Finset.sum_const, smul_eq_mul] using Finset.sum_le_sum hright
    _ ≤ (D-1).choose (t-2) + (D-1) * (D-2).choose (t-3) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hcommon) _
    _ = (t-1) * (D-1).choose (t-2) := by
      rw [hmul]
      have ht' : t-1 = t-2+1 := by omega
      rw [ht']
      ring

theorem source_overlap_card_le {k D t : ℕ} (T : Tournament k)
    (hk : k = 2*D+1) (hout : ∀ v, (outN T v).card = D)
    (ht : 3 ≤ t) (hroom : t-1 ≤ D) (A : Finset (Fin k)) :
    ((sourceSets T t).filter (fun I => 2 ≤ (A ∩ I).card)).card ≤
      A.card.choose 2 * ((t-1) * (D-1).choose (t-2)) := by
  let cover := (A.powersetCard 2).biUnion fun C =>
    (sourceSets T t).filter (fun I => C ⊆ I)
  have hsub : (sourceSets T t).filter (fun I => 2 ≤ (A ∩ I).card) ⊆ cover := by
    intro I hI
    obtain ⟨hI, hAI⟩ := Finset.mem_filter.mp hI
    obtain ⟨C, hC, hcard⟩ := Finset.exists_subset_card_eq hAI
    exact Finset.mem_biUnion.mpr ⟨C,
      Finset.mem_powersetCard.mpr ⟨hC.trans Finset.inter_subset_left, hcard⟩,
      Finset.mem_filter.mpr ⟨hI, hC.trans Finset.inter_subset_right⟩⟩
  have hcount (C : Finset (Fin k)) (hC : C ∈ A.powersetCard 2) :
      ((sourceSets T t).filter (fun I => C ⊆ I)).card ≤
        (t-1) * (D-1).choose (t-2) := by
    obtain ⟨a, b, hne, hCeq⟩ := Finset.card_eq_two.mp
      (Finset.mem_powersetCard.mp hC).2
    rcases T.adj_or_reverse hne with hab | hba
    · simpa only [hCeq, Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        source_star_card_le T hk hout ht hroom hab
    · simpa only [hCeq, Finset.insert_subset_iff, Finset.singleton_subset_iff, and_comm] using
        source_star_card_le T hk hout ht hroom hba
  calc
    ((sourceSets T t).filter (fun I => 2 ≤ (A ∩ I).card)).card ≤ cover.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ C ∈ A.powersetCard 2,
        ((sourceSets T t).filter (fun I => C ⊆ I)).card := Finset.card_biUnion_le
    _ ≤ ∑ _C ∈ A.powersetCard 2, (t-1) * (D-1).choose (t-2) :=
      Finset.sum_le_sum hcount
    _ = A.card.choose 2 * ((t-1) * (D-1).choose (t-2)) := by
      rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard]

def colorExcept {k : ℕ} (I : Finset (Fin k)) (s : Fin k)
    (m : (I.erase s) → Fin 2) (j : I) : Fin 2 :=
  if h : j.val = s then 0
  else m ⟨j.val, Finset.mem_erase.mpr ⟨h, j.property⟩⟩

/-- A source has no incoming internal arc, so its head color may be fixed to
zero. There are only `2^(card I-1)` relevant color assignments. -/
theorem localBad_source_count {k : ℕ} (T : Tournament k) (I : Finset (Fin k))
    (s : Fin k) (hs : IsSource T I s) :
    (localBad T 0 I).card ≤ 2 ^ (I.card-1) * 2 ^ (k*k-I.card.choose 2) := by
  let encoder : I → Fin 0 → I := fun _ h => Fin.elim0 h
  let encoded : Finset (Fin k → Fin k → Fin 2) :=
    (Finset.univ : Finset ((I.erase s) → Fin 2)).biUnion fun m =>
      SensitivityLabelCache12607.SensitivityQ.good T I (colorExcept I s m) encoder
  have hc : (localBad T 0 I).card ≤ encoded.card := by
    apply Finset.card_le_card_of_injOn (fun a : EdgeAssignment k => fun i j => a (i,j))
    · intro a ha
      obtain ⟨m, hm⟩ := (Finset.mem_filter.mp ha).2
      have hcoh (i j : I) (hij : T.Adj i.val j.val) : a (i.val,j.val) = m j.val := by
        by_contra hne
        have hj : j.val ∈ I.filter (fun w => T.Adj i.val w ∧ a (i.val,w) ≠ m w) :=
          Finset.mem_filter.mpr ⟨j.property, hij, hne⟩
        have he : (I.filter (fun w => T.Adj i.val w ∧ a (i.val,w) ≠ m w)) = ∅ :=
          Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hm i.val i.property))
        simpa only [he, Finset.notMem_empty] using hj
      apply Finset.mem_biUnion.mpr
      refine ⟨(fun j => m j.val), by simp only [Finset.mem_univ], ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨by simp only [Finset.mem_univ], ?_⟩
      intro i j hij
      have hno : ¬ ∃ h : Fin 0, encoder i h = j := by
        rintro ⟨h, _⟩
        exact Fin.elim0 h
      rw [if_neg hno]
      have hjs : j.val ≠ s := head_ne_source T I s hs i.property hij
      simpa only [colorExcept, dif_neg hjs] using hcoh i j hij
    · intro a ha b hb hab
      funext ij
      exact congrFun (congrFun hab ij.1) ij.2
  apply hc.trans
  apply Finset.card_biUnion_le.trans
  calc
    (∑ m : (I.erase s) → Fin 2,
        (SensitivityLabelCache12607.SensitivityQ.good T I
          (colorExcept I s m) encoder).card) ≤
      ∑ _m : (I.erase s) → Fin 2, 2 ^ (k*k-I.card.choose 2) :=
        Finset.sum_le_sum (fun m _ =>
          SensitivityLabelCache12607.SensitivityQ.good_card_le T I
            (colorExcept I s m) encoder)
    _ = 2 ^ (I.card-1) * 2 ^ (k*k-I.card.choose 2) := by
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun,
        Fintype.card_coe, Fintype.card_fin, Finset.card_erase_of_mem hs.1]

def sourceProbability (t : ℕ) : ℚ :=
  ((2 ^ (t-1) : ℕ) : ℚ) / ((2 ^ t.choose 2 : ℕ) : ℚ)

theorem localBad_source_probability {k : ℕ} (T : Tournament k)
    (I : Finset (Fin k)) (hs : HasSource T I) :
    ((localBad T 0 I).card : ℚ) ≤
      sourceProbability I.card * Fintype.card (EdgeAssignment k) := by
  obtain ⟨s, hs⟩ := hs
  have hroom : I.card.choose 2 ≤ k*k := by
    rw [← T.card_internalEdges I]
    simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (T.internalEdges I))
  have hpow : (2 : ℚ) ^ I.card.choose 2 * 2 ^ (k*k-I.card.choose 2) = 2 ^ (k*k) := by
    rw [← pow_add, Nat.add_sub_cancel' hroom]
  calc
    ((localBad T 0 I).card : ℚ) ≤
        (2 : ℚ) ^ (I.card-1) * 2 ^ (k*k-I.card.choose 2) := by
      exact_mod_cast localBad_source_count T I s hs
    _ = sourceProbability I.card * Fintype.card (EdgeAssignment k) := by
      simp only [sourceProbability, EdgeAssignment, Fintype.card_fun,
        Fintype.card_prod, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
      rw [← hpow]
      ring




end
end SensitivitySourceLabeling
end



/- Component: Research.Source14567Arithmetic -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
open scoped Classical BigOperators

namespace SensitivitySourceLabeling14567.Arithmetic

abbrev K : ℕ := 14567
abbrev D : ℕ := 7283

def cutoff (q : Fin 5) : ℕ := ![24,31,38,44,50] q

def ordinaryProbability (q : Fin 5) : ℚ :=
  if q.val = 0 then ((2^24 : ℕ) : ℚ) / ((2^276 : ℕ) : ℚ)
  else SensitivityRowCounting.rowProbability 0 q

def size (q : Fin 6) : ℕ :=
  if h : q.val < 5 then cutoff ⟨q.val,h⟩ else 22

def tolerance (q : Fin 6) : ℕ := if q.val < 5 then q.val else 0

def degree (q : Fin 6) : ℕ := (size q).choose 2

def tag (q : Fin 6) : ℕ :=
  if h : q.val < 5 then
    if q.val = 0 then 2^24 else SharperRowLLL.tags 0 ⟨q.val,h⟩
  else 2^21

def coefficientChoose (q : Fin 6) : ℕ :=
  if q.val < 5 then (K-2).choose (size q-2) else 21 * (D-1).choose 20

def coefficient (q : Fin 6) : ℕ :=
  if q.val < 5 then
    (K-2).descFactorial (size q-2) / (size q-2).factorial
  else 21 * ((D-1).descFactorial 20 / (20 : ℕ).factorial)

def probability (q : Fin 6) : ℚ :=
  if h : q.val < 5 then ordinaryProbability ⟨q.val,h⟩
  else ((2^21 : ℕ) : ℚ) / ((2^231 : ℕ) : ℚ)

theorem cutoff_eq_old (q : Fin 5) (hq : q.val ≠ 0) :
    cutoff q = SharperRowLLL.cutoff 0 q := by
  fin_cases q <;> first | contradiction | rfl

theorem elementary (q : Fin 6) : 3 ≤ size q ∧ size q ≤ K ∧ degree q ≤ 1225 := by
  fin_cases q <;> decide

theorem coefficient_exact (q : Fin 6) : coefficientChoose q = coefficient q := by
  unfold coefficientChoose coefficient
  split_ifs <;> rw [Nat.choose_eq_descFactorial_div_factorial]

theorem coefficient_pos (q : Fin 6) : 1 ≤ coefficientChoose q := by
  unfold coefficientChoose
  split_ifs with h
  · apply Nat.choose_pos
    exact Nat.sub_le_sub_right (elementary q).2.1 2
  · have hc : 1 ≤ (D-1).choose 20 := Nat.choose_pos (by decide)
    omega

theorem integer_budget :
    658 * (∑ q : Fin 6, coefficient q * tag q * 329 ^ degree q *
      656 ^ (1225-degree q)) ≤ 2 * 656 ^ 1225 := by
  decide

theorem probability_as_tag (q : Fin 6) :
    probability q = ((tag q : ℕ) : ℚ) / ((2 ^ degree q : ℕ) : ℚ) := by
  fin_cases q <;> rfl

theorem probability_nonneg (q : Fin 6) : 0 ≤ probability q := by
  rw [probability_as_tag]
  positivity

theorem activity_double (q : Fin 6) :
    probability q * ((329 : ℚ)/328) ^ degree q =
      (tag q : ℚ) * ((329 : ℚ)/656) ^ degree q := by
  rw [probability_as_tag]
  simpa only [show (2*329 : ℕ) = 658 by decide, Nat.cast_ofNat,
    show ((658 : ℚ)/656) = (329 : ℚ)/328 by norm_num] using
    SensitivityRowCounting.activity_double (tag q) (degree q) 329 656 (by decide)

theorem activity_budget :
    ∑ q : Fin 6, (coefficientChoose q : ℚ) *
      (probability q * ((329 : ℚ)/328) ^ degree q) ≤ 1 - 1 / ((329 : ℚ)/328) := by
  have h := SensitivityLabelCache12607.SensitivityLLL.rational_power_budget
    coefficient tag degree 1225 329 656 658 (by decide) (by decide)
    (fun q => (elementary q).2.2) integer_budget (by decide)
  simp_rw [coefficient_exact, activity_double]
  convert h using 1 <;> norm_num




end SensitivitySourceLabeling14567.Arithmetic
end



/- Component: Research.Source14567SharedLabeling -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped Classical BigOperators

namespace SensitivitySourceLabeling14567
noncomputable section

open SensitivityLabelCache12607.OAI.Paper320
open SensitivityLabelCache12607.SensitivityQLLL
open SensitivityLabelCache12607.SensitivityCylinder
open Arithmetic
open SensitivitySourceLabeling

def family {k : ℕ} (T : Tournament k) (q : Fin 6) : Finset (Finset (Fin k)) :=
  if q.val < 5 then Finset.univ.powersetCard (size q) else sourceSets T 22

theorem family_card {k : ℕ} (T : Tournament k) (q : Fin 6) (I : Finset (Fin k))
    (hI : I ∈ family T q) : I.card = size q := by
  by_cases hq : q.val < 5
  · exact (Finset.mem_powersetCard.mp (by simpa only [family, if_pos hq] using hI)).2
  · have h := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp
        (by simpa only [family, if_neg hq] using hI : I ∈ sourceSets T 22)).1).2
    simpa only [size, dif_neg hq] using h

def JointIndex {k : ℕ} (T : Tournament k) := Σ q : Fin 6, family T q

instance jointFinite {k : ℕ} (T : Tournament k) : Finite (JointIndex T) := by
  unfold JointIndex
  infer_instance

noncomputable instance jointFintype {k : ℕ} (T : Tournament k) : Fintype (JointIndex T) :=
  Fintype.ofFinite _

noncomputable instance jointDecidableEq {k : ℕ} (T : Tournament k) : DecidableEq (JointIndex T) :=
  Classical.decEq _

def bad {k : ℕ} (T : Tournament k) (i : JointIndex T) : Finset (EdgeAssignment k) :=
  localBad T (tolerance i.1) i.2.val

def neighbors {k : ℕ} (T : Tournament k) (i : JointIndex T) : Finset (JointIndex T) :=
  Finset.univ.filter (fun j => 2 ≤ (i.2.val ∩ j.2.val).card)

theorem localBad_ordinary_probability {k : ℕ} (q : Fin 5) (T : Tournament k)
    (I : Finset (Fin k)) (hI : I.card = cutoff q) :
    ((localBad T q.val I).card : ℚ) ≤
      ordinaryProbability q * Fintype.card (EdgeAssignment k) := by
  by_cases hq : q.val = 0
  · have hq0 : q = 0 := Fin.ext hq
    subst q
    have hcard : I.card = 24 := hI
    rw [show ordinaryProbability (0 : Fin 5) =
      ((2^24 : ℕ) : ℚ) / ((2^276 : ℕ) : ℚ) from rfl]
    simpa only [SensitivityLabelCache12607.SensitivityQLLL.eventProbability,
      Fin.val_zero, hcard, Nat.zero_mul, pow_zero, mul_one,
      EdgeAssignment, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      show (24 : ℕ).choose 2 = 276 by decide] using
      localBad_probability_bound T 0 I
  · have hcard : I.card = SharperRowLLL.cutoff 0 q := hI.trans (cutoff_eq_old q hq)
    simpa only [ordinaryProbability, if_neg hq] using
      SensitivityRowCounting.localBad_row_probability 0 q T I hcard

theorem bad_probability {k : ℕ} (T : Tournament k) (i : JointIndex T) :
    ((bad T i).card : ℚ) ≤ probability i.1 * Fintype.card (EdgeAssignment k) := by
  by_cases hq : i.1.val < 5
  · have hI : i.2.val.card = cutoff ⟨i.1.val,hq⟩ := by
      simpa only [size, dif_pos hq] using family_card T i.1 i.2.val i.2.property
    simpa only [bad, probability, dif_pos hq, tolerance, if_pos hq] using
      localBad_ordinary_probability ⟨i.1.val,hq⟩ T i.2.val hI
  · have hI : i.2.val ∈ sourceSets T 22 := by
      simpa only [family, if_neg hq] using i.2.property
    have hsrc : HasSource T i.2.val := (Finset.mem_filter.mp hI).2
    have hcard : i.2.val.card = 22 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hI).1).2
    simpa only [bad, probability, dif_neg hq, tolerance, if_neg hq,
      hcard, sourceProbability, show (22 : ℕ)-1 = 21 by decide,
      show (22 : ℕ).choose 2 = 231 by decide] using
      localBad_source_probability T i.2.val hsrc

theorem away {k : ℕ} (T : Tournament k) (i : JointIndex T) (S : Finset (JointIndex T))
    (_hi : i ∉ S) (hS : ∀ j ∈ S, j ∉ neighbors T i) :
    ((bad T i ∩ SensitivityLabelCache12607.SensitivityLLL.avoid (bad T) S).card : ℚ) ≤
      probability i.1 *
        ((SensitivityLabelCache12607.SensitivityLLL.avoid (bad T) S).card : ℚ) := by
  let C := T.internalEdges i.2.val
  let E := bad T i
  let F := SensitivityLabelCache12607.SensitivityLLL.avoid (bad T) S
  have hE : DependsOn (ι := Fin k × Fin k) (β := Fin 2) E C :=
    localBad_depends T (tolerance i.1) i.2.val
  have hDis : ∀ j ∈ S, Disjoint C (T.internalEdges j.2.val) := by
    intro j hj
    have hh := hS j hj
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    exact internalEdges_disjoint T i.2.val j.2.val (by omega)
  have hF : ∀ a b : EdgeAssignment k,
      (∀ ij, ij ∉ C → a ij = b ij) → (a ∈ F ↔ b ∈ F) := by
    intro a b hab
    have hlocal (j : JointIndex T) (hj : j ∈ S) : a ∈ bad T j ↔ b ∈ bad T j :=
      localBad_depends T (tolerance j.1) j.2.val a b (fun ij hij =>
        hab ij (fun hc => Finset.disjoint_left.mp (hDis j hj) hc hij))
    change a ∈ SensitivityLabelCache12607.SensitivityLLL.avoid (bad T) S ↔
      b ∈ SensitivityLabelCache12607.SensitivityLLL.avoid (bad T) S
    rw [SensitivityLabelCache12607.SensitivityLLL.mem_avoid,
      SensitivityLabelCache12607.SensitivityLLL.mem_avoid]
    constructor
    · intro ha j hj hb
      exact ha j hj ((hlocal j hj).mpr hb)
    · intro hb j hj ha
      exact hb j hj ((hlocal j hj).mp ha)
  exact bound_inter_card_outside (ι := Fin k × Fin k) (β := Fin 2)
    C E F (probability i.1) hE hF (bad_probability T i)

theorem neighbor_count_below {k d : ℕ} (T : Tournament k)
    (hodd : k = 2*d+1) (hdlo : 21 ≤ d) (hdhi : d ≤ D)
    (hout : ∀ v, (outN T v).card = d)
    (i : JointIndex T) (q : Fin 6) :
    ((neighbors T i).filter (fun j => j.1 = q)).card ≤
      degree i.1 * coefficientChoose q := by
  have hc := family_card T i.1 i.2.val i.2.property
  have hinj : Set.InjOn (fun j : JointIndex T => j.2.val)
      ((neighbors T i).filter (fun j => j.1 = q)) := by
    intro j hj j' hj' hBB
    rcases j with ⟨p,B⟩
    rcases j' with ⟨p',B'⟩
    have hp : p = q := (Finset.mem_filter.mp hj).2
    have hp' : p' = q := (Finset.mem_filter.mp hj').2
    subst p
    subst p'
    have hB : B = B' := Subtype.ext hBB
    subst B'
    rfl
  by_cases hq : q.val < 5
  · have hb := SensitivityLabelCache12607.SensitivityLLL.card_overlap_two_fin_le
      k i.2.val (size q) (by have h := (elementary q).1; omega)
    have hk : k ≤ K := by
      change d ≤ 7283 at hdhi
      change k ≤ 14567
      omega
    have hchoose : (k-2).choose (size q-2) ≤ (K-2).choose (size q-2) :=
      Nat.choose_le_choose _ (Nat.sub_le_sub_right hk 2)
    have hb' := hb.trans (Nat.mul_le_mul_left (i.2.val.card.choose 2) hchoose)
    apply Nat.le_trans ?_ (by
      simpa only [hc, degree, coefficientChoose, if_pos hq] using hb')
    apply Finset.card_le_card_of_injOn (fun j : JointIndex T => j.2.val) ?_ hinj
    intro j hj
    have hjq : j.1 = q := (Finset.mem_filter.mp hj).2
    have hm : j.2.val ∈ Finset.univ.powersetCard (size q) := by
      have h : j.2.val ∈ family T q :=
        Eq.mp (congrArg (fun p => j.2.val ∈ family T p) hjq) j.2.property
      simpa only [family, if_pos hq] using h
    exact Finset.mem_filter.mpr ⟨hm,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2⟩
  · have hb := source_overlap_card_le T hodd hout
      (t := 22) (by decide) hdlo i.2.val
    have hchoose : (d-1).choose 20 ≤ (D-1).choose 20 :=
      Nat.choose_le_choose _ (Nat.sub_le_sub_right hdhi 1)
    have hsmall : (22-1) * (d-1).choose (22-2) ≤ 21 * (D-1).choose 20 :=
      Nat.mul_le_mul_left 21 hchoose
    have hb' := hb.trans (Nat.mul_le_mul_left (i.2.val.card.choose 2) hsmall)
    apply Nat.le_trans ?_ (by
      simpa only [hc, degree, coefficientChoose, if_neg hq] using hb')
    apply Finset.card_le_card_of_injOn (fun j : JointIndex T => j.2.val) ?_ hinj
    intro j hj
    have hjq : j.1 = q := (Finset.mem_filter.mp hj).2
    have hm : j.2.val ∈ sourceSets T 22 := by
      have h : j.2.val ∈ family T q :=
        Eq.mp (congrArg (fun p => j.2.val ∈ family T p) hjq) j.2.property
      simpa only [family, if_neg hq] using h
    exact Finset.mem_filter.mpr ⟨hm,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2⟩

theorem exists_avoiding_below {k d : ℕ} (T : Tournament k)
    (hodd : k = 2*d+1) (hdlo : 21 ≤ d) (hdhi : d ≤ D)
    (hout : ∀ v, (outN T v).card = d) :
    ∃ a : EdgeAssignment k, ∀ i : JointIndex T, a ∉ bad T i := by
  let γ : ℚ := 329/328
  let x : Fin 6 → ℚ := fun q => probability q * γ ^ degree q
  have hγ : 1 < γ := by norm_num [γ]
  have hx0 (q : Fin 6) : 0 ≤ x q :=
    mul_nonneg (probability_nonneg q) (pow_nonneg (by norm_num [γ]) _)
  have hx1 : ∀ q : Fin 6, x q < 1 :=
    SensitivityLabelCache12607.SensitivityLLL.activity_lt_one_of_budget
      x coefficientChoose γ hγ hx0 coefficient_pos activity_budget
  apply SensitivityLabelCache12607.SensitivityLLL.asymmetric_local_lemma (bad T)
    (fun i => probability i.1) (fun i => x i.1) (neighbors T)
    (fun i => hx0 i.1) (fun i => hx1 i.1) ?_ (away T)
  intro i
  exact SensitivityLabelCache12607.SensitivityLLL.rank_one_activity_condition
    (neighbors T i) (fun j => j.1) probability degree coefficientChoose i.1
    γ hγ probability_nonneg hx1
    (neighbor_count_below T hodd hdlo hdhi hout i) activity_budget




theorem mem_localBad_of_rows {k q : ℕ} (T : Tournament k)
    (I : Finset (Fin k)) (a : EdgeAssignment k) (m : Fin k → Fin 2)
    (hrow : ∀ i ∈ I, (I.filter (fun j => T.Adj i j ∧ a (i,j) ≠ m j)).card ≤ q) :
    a ∈ localBad T q I := by
  exact Finset.mem_filter.mpr ⟨by simp only [Finset.mem_univ], m, hrow⟩

theorem labeling_of_avoiding {k : ℕ} (T : Tournament k) (a : EdgeAssignment k)
    (ha : ∀ i : JointIndex T, a ∉ bad T i) :
    ∃ label : Fin k → Fin k → Fin 2,
      (∀ q : Fin 5, SensitivityLabelCache12607.SensitivityQ.DefectBound T label q.val
        (cutoff q)) ∧
      (∀ I : Finset (Fin k), ∀ m : Fin k → Fin 2, HasSource T I →
        (∀ i ∈ I, (I.filter (fun j => T.Adj i j ∧ label i j ≠ m j)).card ≤ 0) →
          I.card < 22) := by
  refine ⟨(fun i j => a (i,j)), ?_, ?_⟩
  · intro q I m hrow
    by_contra hI
    obtain ⟨J,hJI,hJ⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hI)
    let p : Fin 6 := ⟨q.val, by have h := q.isLt; omega⟩
    have hp : p.val < 5 := q.isLt
    have hmem : J ∈ family T p := by
      simp only [family, if_pos hp]
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      simpa only [size, dif_pos hp] using hJ
    let j : JointIndex T := ⟨p,⟨J,hmem⟩⟩
    apply ha j
    change a ∈ localBad T (tolerance p) J
    rw [tolerance, if_pos hp]
    apply mem_localBad_of_rows T J a m
    intro i hi
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hJI)).trans
      (hrow i (hJI hi))
  · intro I m hsource hrow
    by_contra hI
    obtain ⟨s,hs⟩ := hsource
    have herase : 21 ≤ (I.erase s).card := by
      rw [Finset.card_erase_of_mem hs.1]
      omega
    obtain ⟨R,hRI,hR⟩ := Finset.exists_subset_card_eq herase
    have hsR : s ∉ R := by
      intro hsR
      exact Finset.notMem_erase s I (hRI hsR)
    let J := insert s R
    have hJI : J ⊆ I := Finset.insert_subset_iff.mpr
      ⟨hs.1, hRI.trans (Finset.erase_subset _ _)⟩
    have hJ : J.card = 22 := by
      rw [Finset.card_insert_of_notMem hsR, hR]
    have hsrcJ : HasSource T J :=
      ⟨s, Finset.mem_insert_self _ _, fun j hj hjs => hs.2 j (hJI hj) hjs⟩
    have hmem : J ∈ family T 5 := by
      simp only [family, show ¬ ((5 : Fin 6).val < 5) by decide, if_false]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hJ⟩, hsrcJ⟩
    let j : JointIndex T := ⟨5,⟨J,hmem⟩⟩
    apply ha j
    change a ∈ localBad T 0 J
    apply mem_localBad_of_rows T J a m
    intro i hi
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hJI)).trans
      (hrow i (hJI hi))

theorem labeling_exists_below {k d : ℕ} (T : Tournament k)
    (hodd : k = 2*d+1) (hdlo : 21 ≤ d) (hdhi : d ≤ D)
    (hout : ∀ v, (outN T v).card = d) :
    ∃ label : Fin k → Fin k → Fin 2,
      (∀ q : Fin 5, SensitivityLabelCache12607.SensitivityQ.DefectBound T label q.val
        (cutoff q)) ∧
      (∀ I : Finset (Fin k), ∀ m : Fin k → Fin 2, HasSource T I →
        (∀ i ∈ I, (I.filter (fun j => T.Adj i j ∧ label i j ≠ m j)).card ≤ 0) →
          I.card < 22) := by
  obtain ⟨a,ha⟩ := exists_avoiding_below T hodd hdlo hdhi hout
  exact labeling_of_avoiding T a ha







/-- One checked upper budget covers every smaller regular odd tournament. -/
theorem shared_labeling_source_below_14567_lll {k d : ℕ}
    (hodd : k = 2*d+1) (hdlo : 21 ≤ d) (hdhi : d ≤ 7283)
    (A : Fin k → Fin k → Prop)
    (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i))
    (hout : ∀ i, (Finset.univ.filter (A i)).card = d) :
    ∃ label : Fin k → Fin k → Fin 2,
      (∀ q : Fin 5, ∀ I : Finset (Fin k), ∀ colors : Fin k → Fin 2,
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ q.val) →
          I.card < (![24,31,38,44,50] q)) ∧
      (∀ I : Finset (Fin k), ∀ colors : Fin k → Fin 2,
        (∃ s ∈ I, ∀ j ∈ I, j ≠ s → A s j) →
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ 0) →
          I.card < 22) := by
  let T : Tournament k := { Adj := A, loopless := hloop, edge_compl := hcomp }
  obtain ⟨label,hdefect,hsource⟩ := labeling_exists_below T hodd hdlo hdhi hout
  exact ⟨label,hdefect,hsource⟩








end
end SensitivitySourceLabeling14567
end



/- Component: Research.GenericAPI -/
section
/-!
Actual finite Boolean witnesses for every repetition of a coupled periodic
construction. The shared tournament labeling is supplied by the cited public
raw-label theorem. Historical comments in the retained foundation record its
source provenance. Exponent conversion is proved in a separate theorem.
-/

/- Bundled unchanged module: Definitions.Local2075Foundation -/

/-!
Complete proof of SensitivityCampaign.AchievesExponent (2.075 : ℝ).

Reuses the accepted Prove2Me 2.0635 proof by abhishekdpseok, submission
f80a3f37-72fa-4d56-a094-3e4d351764f3, and the checked tasks 1 and 2.
See README.md for component provenance, exact constants, and verification.
Generated by bundle.py from the accompanying modules.
-/

/- Component 1: CoupledFoundation.lean -/
section Bundle2075_1

/-
Block sensitivity versus sensitivity: exponent at least 2.0635.
Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

Foundations reuse the proved OpenAI/math sensitivity development and the
accepted Prove2Me 2.05 solution by robinkothari (theorem
4807ab9c-ddde-49d8-83cf-3532a7f795c3). The finite binomial labeling estimate
also follows the accepted 2.0391 proof (theorem
872a88de-6ec2-46b6-a079-9afd4617aa55).
The coupled repair estimate and seven-layer certificate are supplied here.
All theorem proofs are included; the only platform import is the unchanged
campaign definition. The target theorem is not imported.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveProfiles -/

namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320

/-- Acceptance at a stronger index implies acceptance at every weaker index. -/
structure NestedFamily {h : ℕ} {I : Type}
    (F : Fin h → (I → Bool) → Bool) : Prop where
  accepts_of_le : ∀ {q q' : Fin h} {x}, q ≤ q' → F q' x = true → F q x = true

theorem NestedFamily.rejects_of_le {h : ℕ} {I : Type}
    {F : Fin h → (I → Bool) → Bool} (hF : NestedFamily F)
    {q q' : Fin h} {x} (hqq : q ≤ q') (hx : F q x = false) :
    F q' x = false := by
  cases h' : F q' x
  · rfl
  · have := hF.accepts_of_le hqq h'
    simp [hx] at this

/-- The number of coordinates whose one-bit flip changes both predicates. -/
def jointSensitivityAt {I : Type} [Fintype I]
    (f g : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i =>
    f (flip x {i}) ≠ f x ∧ g (flip x {i}) ≠ g x).card




























end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Basic -/

namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}
















theorem flip_prod_same (x : J × I → Bool) (j : J) (i : I) :
    (fun a => flip x {(j, i)} (j, a)) = flip (fun a => x (j, a)) {i} := by
  funext a
  simp [flip]

theorem flip_prod_other (x : J × I → Bool) {j k : J} (i : I) (hk : k ≠ j) :
    (fun a => flip x {(j, i)} (k, a)) = fun a => x (k, a) := by
  funext a
  simp [flip, hk]




section Finite

variable [Fintype I]




theorem sensitivityAt_le_card (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ Fintype.card I :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem sensitivityAt_le_sensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ sensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

theorem sensitivity_le (f : (I → Bool) → Bool) {n : ℕ}
    (h : ∀ x, sensitivityAt f x ≤ n) : sensitivity f ≤ n :=
  Finset.sup_le fun x _ => h x
















theorem le_blockSensitivityAt (f : (I → Bool) → Bool) (x : I → Bool)
    (blocks : Finset (Finset I))
    (hd : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B)
    (hb : ∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) :
    blocks.card ≤ blockSensitivityAt f x := by
  have h := Finset.le_sup (s := (Finset.univ : Finset (Finset (Finset I))))
    (f := fun blocks =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
      then blocks.card else 0) (Finset.mem_univ blocks)
  have hv : (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) := ⟨hd, hb⟩
  simpa only [blockSensitivityAt, if_pos hv] using h

theorem blockSensitivityAt_le (f : (I → Bool) → Bool) (x : I → Bool) {n : ℕ}
    (h : ∀ blocks : Finset (Finset I),
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) →
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) → blocks.card ≤ n) :
    blockSensitivityAt f x ≤ n := by
  apply Finset.sup_le
  intro blocks _
  split_ifs with hb
  · exact h blocks hb.1 hb.2
  · exact Nat.zero_le _




theorem le_blockSensitivityAt_of_family [Fintype K]
    (f : (I → Bool) → Bool) (x : I → Bool) (blocks : K → Finset I)
    (hne : ∀ k, (blocks k).Nonempty)
    (hd : Pairwise fun k l => Disjoint (blocks k) (blocks l))
    (hb : ∀ k, f (flip x (blocks k)) ≠ f x) :
    Fintype.card K ≤ blockSensitivityAt f x := by
  have hinj : Function.Injective blocks := by
    intro k l hkl
    by_contra hnekl
    obtain ⟨i, hi⟩ := hne k
    exact Finset.disjoint_left.mp (hd hnekl) hi (by simpa [← hkl] using hi)
  have hcard := le_blockSensitivityAt f x (Finset.univ.image blocks)
    (by
      intro A hA B hB hAB
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hB
      exact hd (fun h => hAB (congrArg blocks h)))
    (by
      intro B hB
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hB
      exact ⟨hne k, hb k⟩)
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using hcard







end Finite
end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Tournament -/

namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

structure Tournament (k : ℕ) extends Digraph (Fin k) where
  loopless : ∀ i, ¬ Adj i i
  edge_compl : ∀ {i j}, i ≠ j → (Adj i j ↔ ¬ Adj j i)

structure RegularTournament (M : ℕ) extends Tournament (2 * M^2 + 1) where
  outdegree : ∀ i, (Finset.univ.filter (Adj i)).card = M^2

structure GoodLabeling {k : ℕ} (T : Tournament k) (r : ℕ) where
  label : Fin k → Fin k → Fin r
  good : ∀ I : Finset (Fin k), I.card = 16 → ∀ m : Fin k → Fin r,
    ∃ i ∈ I, ∃ j ∈ I, T.Adj i j ∧ label i j ≠ m j

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h

theorem not_adj_reverse {i j : Fin k} (h : T.Adj i j) : ¬ T.Adj j i :=
  (T.edge_compl (T.ne_of_adj h)).mp h

theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)

theorem internal_sink_unique {I : Finset (Fin k)} {i j : Fin k}
    (hi : i ∈ I) (hj : j ∈ I)
    (hsi : ∀ v ∈ I, ¬ T.Adj i v) (hsj : ∀ v ∈ I, ¬ T.Adj j v) : i = j := by
  by_contra h
  rcases T.adj_or_reverse h with hh | hh
  · exact hsi j hj hh
  · exact hsj i hi hh

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)




end GoodLabeling
end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveDefinitions -/

namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

def recursiveChild {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) : I → Bool :=
  fun a => x ((j, c), a)

def gateIndex {h : ℕ} (q : Fin h) : Fin (h + 1) := (Fin.rev q).castSucc

theorem gateIndex_lt_last {h : ℕ} (q : Fin h) : gateIndex q < Fin.last h :=
  Fin.castSucc_lt_last _







/-- A clause uses every target in its own row and one labeled gate per outgoing edge. -/
def rowClause {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Bool :=
  decide ((∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
    ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false)

/-- The next-level predicate is the disjunction of the literal row clauses. -/
def recursiveFamily {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Bool :=
  decide (∃ i, rowClause T label F q x i = true)

theorem rowClause_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    rowClause T label F q x i = true ↔
      (∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp only [rowClause, decide_eq_true_eq]

theorem recursiveFamily_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = true ↔ ∃ i, rowClause T label F q x i = true := by
  simp only [recursiveFamily, decide_eq_true_eq]

theorem recursiveFamily_eq_false_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = false ↔ ∀ i, rowClause T label F q x i = false := by
  simp [recursiveFamily]













end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveBlocks -/

namespace OAI

/-! Disjoint zero-input blocks lift to every column of a chosen row. -/

noncomputable section
open scoped Classical

namespace Paper320

def rowLift {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I) :
    Finset ((Fin k × Fin r) × I) :=
  (Finset.univ.product B).map
    ⟨fun p : Fin r × I => ((i, p.1), p.2), by
      intro p q hpq
      exact Prod.ext (congrArg (fun z => z.1.2) hpq) (congrArg (fun z : (Fin k × Fin r) × I => z.2) hpq)⟩

@[simp] theorem mem_rowLift {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I)
    (p : (Fin k × Fin r) × I) : p ∈ rowLift (r := r) i B ↔ p.1.1 = i ∧ p.2 ∈ B := by
  rcases p with ⟨⟨j, c⟩, a⟩
  unfold rowLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨⟨c', b⟩, hb, hp⟩
    change ((i, c'), b) = ((j, c), a) at hp
    cases hp
    exact ⟨rfl, (Finset.mem_product.mp hb).2⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨(c, a), Finset.mem_product.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
















theorem recursiveChild_rowLift_same {k r : ℕ} {I : Type}
    (i : Fin k) (B : Finset I) (c : Fin r) :
    recursiveChild (flip (fun _ => false) (rowLift (r := r) i B)) i c =
      flip (fun _ => false) B := by
  funext a
  simp [recursiveChild, flip]

theorem recursiveChild_rowLift_other {k r : ℕ} {I : Type}
    (i j : Fin k) (B : Finset I) (c : Fin r) (hji : j ≠ i) :
    recursiveChild (flip (fun _ => false) (rowLift (r := r) i B)) j c =
      fun _ => false := by
  funext a
  simp [recursiveChild, flip, hji]




end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveFlips -/

namespace OAI

/-! A raw bit belongs to one child and changes at most one condition of a clause. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursiveChild_flip_same {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) (a : I) :
    recursiveChild (flip x {((j, c), a)}) j c = flip (recursiveChild x j c) {a} :=
  flip_prod_same x (j, c) a

theorem recursiveChild_flip_other {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j j' : Fin k) (c c' : Fin r) (a : I)
    (h : (j', c') ≠ (j, c)) :
    recursiveChild (flip x {((j, c), a)}) j' c' = recursiveChild x j' c' :=
  flip_prod_other x a h

theorem rowClause_eq_of_conditions {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x y : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (ht : ∀ c, F (Fin.last h) (recursiveChild x i c) =
      F (Fin.last h) (recursiveChild y i c))
    (hg : ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) =
      F (gateIndex q) (recursiveChild y j (label i j))) :
    rowClause T label F q x i = rowClause T label F q y i := by
  apply Bool.eq_iff_iff.mpr
  rw [rowClause_eq_true_iff, rowClause_eq_true_iff]
  constructor
  · rintro ⟨hxt, hxg⟩
    exact ⟨fun c => (ht c).symm.trans (hxt c),
      fun j hij => (hg j hij).symm.trans (hxg j hij)⟩
  · rintro ⟨hyt, hyg⟩
    exact ⟨fun c => (ht c).trans (hyt c),
      fun j hij => (hg j hij).trans (hyg j hij)⟩

theorem rowClause_flip_eq {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (ht : j = i → F (Fin.last h) (flip (recursiveChild x j c) {a}) =
      F (Fin.last h) (recursiveChild x j c))
    (hg : T.Adj i j → c = label i j →
      F (gateIndex q) (flip (recursiveChild x j c) {a}) =
        F (gateIndex q) (recursiveChild x j c)) :
    rowClause T label F q (flip x {((j, c), a)}) i = rowClause T label F q x i := by
  apply rowClause_eq_of_conditions
  · intro c'
    by_cases heq : (i, c') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact ht rfl
    · rw [recursiveChild_flip_other x j i c c' a heq]
  · intro j' hij'
    by_cases heq : (j', label i j') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact hg hij' rfl
    · rw [recursiveChild_flip_other x j j' c (label i j') a heq]

theorem rowClause_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c)) := by
  by_contra hn
  apply hc
  apply rowClause_flip_eq
  · intro hji
    by_contra hne
    exact hn (Or.inl ⟨hji, hne⟩)
  · intro hij hcl
    by_contra hne
    exact hn (Or.inr ⟨hij, hcl, hne⟩)

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveSets -/

namespace OAI

/-! Finite sets of changing raw coordinates inside an individual child. -/

noncomputable section
open scoped Classical

namespace Paper320

def childLift {J I : Type} (j : J) (A : Finset I) : Finset (J × I) :=
  A.map ⟨fun a => (j, a), fun _ _ h => congrArg (fun p : J × I => p.2) h⟩

@[simp] theorem mem_childLift {J I : Type} (j : J) (A : Finset I) (p : J × I) :
    p ∈ childLift j A ↔ p.1 = j ∧ p.2 ∈ A := by
  rcases p with ⟨k, a⟩
  unfold childLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hp⟩
    change (j, b) = (k, a) at hp
    cases hp
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp] theorem childLift_card {J I : Type} (j : J) (A : Finset I) :
    (childLift j A).card = A.card := Finset.card_map _




def childJointChanges {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (j, c) (Finset.univ.filter fun a =>
    F q (flip (recursiveChild x j c) {a}) ≠ F q (recursiveChild x j c) ∧
    F q' (flip (recursiveChild x j c) {a}) ≠ F q' (recursiveChild x j c))




@[simp] theorem childJointChanges_card {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    (childJointChanges F q q' x j c).card =
      jointSensitivityAt (F q) (F q') (recursiveChild x j c) := by
  simp [childJointChanges, jointSensitivityAt]

theorem card_biUnion_le_mul {J I : Type} [DecidableEq I] (A : Finset J) (B : J → Finset I) (n : ℕ)
    (hn : ∀ j ∈ A, (B j).card ≤ n) : (A.biUnion B).card ≤ A.card * n := by
  calc
    (A.biUnion B).card ≤ ∑ j ∈ A, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A, n := Finset.sum_le_sum hn
    _ = A.card * n := by simp




end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.TournamentCounts -/

namespace OAI

/-! The exact internal edge count and the small gate-candidate bound. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

def internalEdges (I : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (I ×ˢ I).filter fun p => T.Adj p.1 p.2

theorem card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by
  let U := T.internalEdges I
  let V := (I ×ˢ I).filter fun p => T.Adj p.2 p.1
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact T.not_adj_reverse (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion V hd = I.offDiag := by
    ext ⟨i,j⟩
    simp only [Finset.mem_disjUnion, U, V, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hi,hj⟩,h⟩ | ⟨⟨hi,hj⟩,h⟩)
      · exact ⟨hi,hj,T.ne_of_adj h⟩
      · exact ⟨hi,hj,(T.ne_of_adj h).symm⟩
    · rintro ⟨hi,hj,hne⟩
      exact (T.adj_or_reverse hne).imp (fun h => ⟨⟨hi,hj⟩,h⟩) (fun h => ⟨⟨hi,hj⟩,h⟩)
  have hs : U.card = V.card := Finset.card_equiv (Equiv.prodComm (Fin k) (Fin k)) (by
    intro p
    simp only [U,V,internalEdges,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

theorem sum_outdegree_eq (I : Finset (Fin k)) :
    ∑ i ∈ I, (I.filter (T.Adj i)).card = (T.internalEdges I).card := by
  simp only [internalEdges, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

theorem card_le_three_of_outdegree_le_one (I : Finset (Fin k))
    (h : ∀ i ∈ I, (I.filter (T.Adj i)).card ≤ 1) : I.card ≤ 3 := by
  have hsum := Finset.sum_le_sum h
  have hc : I.card.choose 2 ≤ I.card := by
    rw [← T.card_internalEdges, ← T.sum_outdegree_eq]
    simpa only [Finset.sum_const_nat, mul_one] using hsum
  have hdouble : I.card * (I.card - 1) ≤ 2 * I.card + 1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have h4 : 4 ≤ I.card := by omega
  have ht : I.card - 1 + 1 = I.card := by omega
  nlinarith

end Paper320.Tournament

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveFailures -/

namespace OAI

/-! Fixed initial-input lists of clauses with exactly one failed condition. -/

noncomputable section
open scoped Classical

namespace Paper320

def targetFailures {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin r) :=
  Finset.univ.filter fun c => F (Fin.last h) (recursiveChild x i c) = false

def gateFailures {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun j => T.Adj i j ∧
    F (gateIndex q) (recursiveChild x j (label i j)) = true

def targetCandidates {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => (targetFailures F x i).card = 1 ∧ gateFailures T label F q x i = ∅

def gateCandidates {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => targetFailures F x i = ∅ ∧ (gateFailures T label F q x i).card = 1

def targetWitness {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k) : Fin r :=
  if hi : (targetFailures F x i).Nonempty then hi.choose else ⟨0, hr⟩

def gateWitness {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Fin k :=
  if hi : (gateFailures T label F q x i).Nonempty then hi.choose else i

theorem targetFailures_empty_iff {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    targetFailures F x i = ∅ ↔ ∀ c, F (Fin.last h) (recursiveChild x i c) = true := by
  simp [targetFailures, Finset.filter_eq_empty_iff]

theorem gateFailures_empty_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    gateFailures T label F q x i = ∅ ↔
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp [gateFailures, Finset.filter_eq_empty_iff]

theorem targetFailures_singleton {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) :
    targetFailures F x i = {targetWitness F x hr i} := by
  have hc := (Finset.mem_filter.mp hi).2.1
  obtain ⟨c, hc'⟩ := Finset.card_eq_one.mp hc
  have hne : (targetFailures F x i).Nonempty := hc' ▸ Finset.singleton_nonempty c
  have hm : targetWitness F x hr i ∈ targetFailures F x i := by
    simp only [targetWitness, dif_pos hne]
    exact hne.choose_spec
  rw [hc', Finset.mem_singleton] at hm
  simpa [hm] using hc'

theorem gateFailures_singleton {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) :
    gateFailures T label F q x i = {gateWitness T label F q x i} := by
  have hc := (Finset.mem_filter.mp hi).2.2
  obtain ⟨j, hc'⟩ := Finset.card_eq_one.mp hc
  have hne : (gateFailures T label F q x i).Nonempty := hc' ▸ Finset.singleton_nonempty j
  have hm : gateWitness T label F q x i ∈ gateFailures T label F q x i := by
    simp only [gateWitness, dif_pos hne]
    exact hne.choose_spec
  rw [hc', Finset.mem_singleton] at hm
  simpa [hm] using hc'




theorem gateCandidates_neighbor {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x) (hij : T.Adj i j) :
    j = gateWitness T label F q x i := by
  have ht := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hj).2.1
  have hon := hF.accepts_of_le (gateIndex_lt_last q).le (ht (label i j))
  have hm : j ∈ gateFailures T label F q x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hon⟩
  rwa [gateFailures_singleton T label F q x i hi, Finset.mem_singleton] at hm

theorem gateCandidates_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    (gateCandidates T label F q x).card ≤ 3 := by
  apply T.card_le_three_of_outdegree_le_one
  intro i hi
  apply le_trans (Finset.card_le_card (t := {gateWitness T label F q x i}) ?_)
    (by simp)
  intro j hj
  have h := Finset.mem_filter.mp hj
  exact Finset.mem_singleton.mpr (gateCandidates_neighbor T label F hF q x i j hi h.1 h.2)

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveRepair -/

namespace OAI

/-! A successful raw-bit flip repairs the unique initial failed condition. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem repaired_target_location {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c c' : Fin r) (a : I)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true)
    (hz : F (Fin.last h) (recursiveChild x i c') = false) : (i, c') = (j, c) := by
  by_contra hne
  have ht := ((rowClause_eq_true_iff T label F q _ i).mp hf).1 c'
  rw [recursiveChild_flip_other x j i c c' a hne, hz] at ht
  exact Bool.false_ne_true ht

theorem repaired_gate_location {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j j' : Fin k) (c : Fin r) (a : I)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true)
    (hij' : T.Adj i j') (hon : F (gateIndex q) (recursiveChild x j' (label i j')) = true) :
    (j', label i j') = (j, c) := by
  by_contra hne
  have hg := ((rowClause_eq_true_iff T label F q _ i).mp hf).2 j' hij'
  rw [recursiveChild_flip_other x j j' c (label i j') a hne, hon] at hg
  exact Bool.false_ne_true hg.symm

theorem rowClause_repair_cases {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hi : rowClause T label F q x i = false)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true) :
    (i ∈ targetCandidates T label F q x ∧ j = i ∧
      F (Fin.last h) (recursiveChild x j c) = false ∧
      F (Fin.last h) (flip (recursiveChild x j c) {a}) = true) ∨
    (i ∈ gateCandidates T label F q x ∧ T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (recursiveChild x j c) = true ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) = false) := by
  have hchange : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
    simp [hi, hf]
  rcases rowClause_flip_change T label F q x i j c a hchange with
    ⟨hji, ht⟩ | ⟨hij, rfl, hg⟩
  · subst j
    have hton := ((rowClause_eq_true_iff T label F q _ i).mp hf).1 c
    rw [recursiveChild_flip_same] at hton
    have htoff : F (Fin.last h) (recursiveChild x i c) = false := by
      cases hc : F (Fin.last h) (recursiveChild x i c)
      · rfl
      · exact False.elim (ht (hton.trans hc.symm))
    have htargets : targetFailures F x i = {c} := by
      ext c'
      simp only [targetFailures, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hfalse
        exact congrArg Prod.snd (repaired_target_location T label F q x i i c c' a hf hfalse)
      · rintro rfl
        exact htoff
    have hgates : gateFailures T label F q x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j' hj'
      have h := (Finset.mem_filter.mp hj').2
      have heq := repaired_gate_location T label F q x i i j' c a hf h.1 h.2
      exact T.ne_of_adj h.1 (congrArg Prod.fst heq).symm
    have hmem : i ∈ targetCandidates T label F q x := by
      simp [targetCandidates, htargets, hgates]
    exact Or.inl ⟨hmem, rfl, htoff, hton⟩
  · have hgoff := ((rowClause_eq_true_iff T label F q _ i).mp hf).2 j hij
    rw [recursiveChild_flip_same] at hgoff
    have hgon : F (gateIndex q) (recursiveChild x j (label i j)) = true := by
      cases hc : F (gateIndex q) (recursiveChild x j (label i j))
      · exact False.elim (hg (hgoff.trans hc.symm))
      · rfl
    have htargets : targetFailures F x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c' hc'
      have heq := repaired_target_location T label F q x i j (label i j) c' a hf
        (Finset.mem_filter.mp hc').2
      exact T.ne_of_adj hij (congrArg Prod.fst heq)
    have hgates : gateFailures T label F q x i = {j} := by
      ext j'
      simp only [gateFailures, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hij', hon⟩
        exact congrArg Prod.fst (repaired_gate_location T label F q x i j j' (label i j) a hf hij' hon)
      · rintro rfl
        exact ⟨hij, hgon⟩
    have hmem : i ∈ gateCandidates T label F q x := by
      simp [gateCandidates, htargets, hgates]
    exact Or.inr ⟨hmem, hij, rfl, hgon, hgoff⟩

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveCandidates -/

namespace OAI

/-! Unique failed children and the unique possible sink of the gate-clause list. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem targetWitness_false {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) :
    F (Fin.last h) (recursiveChild x i (targetWitness F x hr i)) = false := by
  have hm : targetWitness F x hr i ∈ targetFailures F x i := by
    rw [targetFailures_singleton T label F q x hr i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

theorem targetWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) (c : Fin r)
    (hc : F (Fin.last h) (recursiveChild x i c) = false) : c = targetWitness F x hr i := by
  have hm : c ∈ targetFailures F x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  rwa [targetFailures_singleton T label F q x hr i hi, Finset.mem_singleton] at hm

theorem gateWitness_spec {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) :
    T.Adj i (gateWitness T label F q x i) ∧
      F (gateIndex q) (recursiveChild x (gateWitness T label F q x i)
        (label i (gateWitness T label F q x i))) = true := by
  have hm : gateWitness T label F q x i ∈ gateFailures T label F q x i := by
    rw [gateFailures_singleton T label F q x i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

theorem gateWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) (j : Fin k) (hij : T.Adj i j)
    (hj : F (gateIndex q) (recursiveChild x j (label i j)) = true) :
    j = gateWitness T label F q x i := by
  have hm : j ∈ gateFailures T label F q x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hj⟩
  rwa [gateFailures_singleton T label F q x i hi, Finset.mem_singleton] at hm

def gateSinks {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  (gateCandidates T label F q x).filter fun i =>
    ∀ j ∈ gateCandidates T label F q x, ¬ T.Adj i j

theorem gateSinks_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    (gateSinks T label F q x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact T.internal_sink_unique (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem nonsink_gateWitness_mem {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i : Fin k) (hi : i ∈ gateCandidates T label F q x)
    (hs : i ∉ gateSinks T label F q x) :
    gateWitness T label F q x i ∈ gateCandidates T label F q x := by
  have he : ∃ j ∈ gateCandidates T label F q x, T.Adj i j := by
    by_contra hn
    apply hs
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    intro j hj hij
    exact hn ⟨j, hj, hij⟩
  obtain ⟨j, hj, hij⟩ := he
  rwa [← gateCandidates_neighbor T label F hF q x i j hi hj hij]

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Composition -/

namespace OAI

/-! Disjoint Boolean composition, with each child retaining its own raw coordinates. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I J : Type}













section Finite
variable [Fintype I] [Fintype J]










end Finite
end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Reindex -/

namespace OAI

/-! Coordinate equivalences preserve the two literal Boolean complexity measures. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J : Type}

def reindex (e : I ≃ J) (f : (I → Bool) → Bool) : (J → Bool) → Bool :=
  fun x => f (fun i => x (e i))

theorem flip_reindex (e : I ≃ J) (x : J → Bool) (B : Finset I) :
    (fun i => flip x (B.map e.toEmbedding) (e i)) =
      flip (fun i => x (e i)) B := by
  funext i
  simp [flip]

theorem flip_reindex_singleton (e : I ≃ J) (x : J → Bool) (i : I) :
    (fun a => flip x {e i} (e a)) = flip (fun a => x (e a)) {i} := by
  simpa using flip_reindex e x {i}

@[simp] theorem reindex_symm (e : I ≃ J) (f : (I → Bool) → Bool) :
    reindex e.symm (reindex e f) = f := by
  funext x
  simp [reindex]

section Finite
variable [Fintype I] [Fintype J]

theorem sensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool) (x : J → Bool) :
    sensitivityAt (reindex e f) x = sensitivityAt f (fun i => x (e i)) := by
  have hs : (Finset.univ.filter fun j =>
      reindex e f (flip x {j}) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (flip (fun a => x (e a)) {i}) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => flip x {e i} (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [flip_reindex_singleton]
  simpa only [sensitivityAt, Finset.card_map] using congrArg Finset.card hs

theorem sensitivity_reindex (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by
  apply Nat.le_antisymm
  · apply sensitivity_le
    intro x
    rw [sensitivityAt_reindex]
    exact sensitivityAt_le_sensitivity f _
  · apply sensitivity_le
    intro x
    have h := sensitivityAt_le_sensitivity (reindex e f) (fun j => x (e.symm j))
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

theorem blockSensitivityAt_le_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt f (fun i => x (e i)) ≤ blockSensitivityAt (reindex e f) x := by
  apply blockSensitivityAt_le
  intro blocks hd hb
  have h := le_blockSensitivityAt_of_family (reindex e f) x
    (fun B : blocks => B.val.map e.toEmbedding)
    (fun B => (hb B.val B.property).1.map (f := e.toEmbedding))
    (by
      intro A B hAB
      apply (Finset.disjoint_map e.toEmbedding).mpr
      exact hd A.val A.property B.val B.property (fun h => hAB (Subtype.ext h)))
    (by
      intro B
      change f (fun i => flip x (B.val.map e.toEmbedding) (e i)) ≠ _
      rw [flip_reindex]
      exact (hb B.val B.property).2)
  simpa only [Fintype.card_coe] using h

theorem blockSensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt (reindex e f) x = blockSensitivityAt f (fun i => x (e i)) := by
  apply Nat.le_antisymm
  · have h := blockSensitivityAt_le_reindex e.symm (reindex e f) (fun i => x (e i))
    simpa only [Equiv.apply_symm_apply, reindex_symm] using h
  · exact blockSensitivityAt_le_reindex e f x




end Finite
end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.TournamentCyclic -/

namespace OAI

/-! The literal regular tournament on an odd cyclic set. -/

noncomputable section
open scoped Classical

namespace Paper320

def cyclicTournament (a : ℕ) : Tournament (2*a+1) where
  Adj i j := 0 < (j-i).val ∧ (j-i).val ≤ a
  loopless i := by simp
  edge_compl := by
    intro i j hij
    have hδ : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
    have hp : 0 < (j-i).val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hδ)
    have hb := (j-i).isLt
    have hn : (i-j).val = 2*a+1-(j-i).val := by
      rw [← neg_sub j i, Fin.val_neg, if_neg hδ]
    change (0 < (j-i).val ∧ (j-i).val ≤ a) ↔ ¬ (0 < (i-j).val ∧ (i-j).val ≤ a)
    rw [hn]
    omega

theorem cyclicTournament_outdegree (a : ℕ) (i : Fin (2*a+1)) :
    (Finset.univ.filter ((cyclicTournament a).Adj i)).card = a := by
  let z : Fin (2*a+1) := 0
  let b : Fin (2*a+1) := ⟨a, by omega⟩
  have he : (Finset.Ioc z b).card =
      (Finset.univ.filter ((cyclicTournament a).Adj i)).card :=
    Finset.card_equiv (Equiv.addLeft i) (by
      intro x
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_univ, true_and]
      change (0 < x.val ∧ x.val ≤ a) ↔
        (0 < ((i+x)-i).val ∧ ((i+x)-i).val ≤ a)
      rw [add_sub_cancel_left])
  rw [← he, Fin.card_Ioc]
  change a - 0 = a
  exact Nat.sub_zero a




end Paper320

end

end OAI

-- Source component: Solutions/Transfer.lean
section Component9

open OAI.Paper320
open scoped Classical

namespace Sensitivity205
noncomputable section

structure Labeling {k : ℕ} (T : Tournament k) (r t : ℕ) where
  label : Fin k → Fin k → Fin r
  coherent_card : ∀ (I : Finset (Fin k)) (m : Fin k → Fin r),
    (∀ i ∈ I, ∀ j ∈ I, T.Adj i j → label i j = m j) → I.card < t

theorem targetCandidates_card {k r h t : ℕ} {I : Type}
    (T : Tournament k) (A : Labeling T r t)
    (F : Fin (h+1) → (I → Bool) → Bool) (hF : NestedFamily F)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (targetCandidates T A.label F q x).card < t := by
  apply A.coherent_card _ (targetWitness F x hr)
  intro i hi j hj hij
  have hgate := (gateFailures_empty_iff T A.label F q x i).mp
    (Finset.mem_filter.mp hi).2.2 j hij
  have htarget := hF.rejects_of_le (gateIndex_lt_last q).le hgate
  exact targetWitness_unique T A.label F q x hr j hj (A.label i j) htarget

def PairBound {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (b : Bool) (V : Fin n → Fin n → ℕ) : Prop :=
  ∀ (q q' : Fin n), q ≤ q' → ∀ x, F q x = b → F q' x = b →
    jointSensitivityAt (F q) (F q') x ≤ V q q'

@[simp] theorem joint_self {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) :
    jointSensitivityAt f f x = sensitivityAt f x := by
  simp [jointSensitivityAt, sensitivityAt]

theorem PairBound.self {n : ℕ} {I : Type} [Fintype I]
    {F : Fin n → (I → Bool) → Bool} {b : Bool} {V : Fin n → Fin n → ℕ}
    (hV : PairBound F b V) (q : Fin n) (x : I → Bool) (hx : F q x = b) :
    sensitivityAt (F q) x ≤ V q q := by
  simpa using hV q q le_rfl x hx hx


end
end Sensitivity205

end Component9

-- Source component: Solutions/Base.lean
section Component10

open OAI.Paper320
open scoped Classical BigOperators

namespace Sensitivity205
noncomputable section










































end
end Sensitivity205

end Component10


namespace Sensitivity205
noncomputable section
open OAI.Paper320
open scoped Classical






















structure Blocks {I : Type} {h : ℕ} (F : Fin h → (I → Bool) → Bool) (n : ℕ) where
  zero : ∀ q, F q (fun _ => false) = false
  sets : Fin n → Finset I
  nonempty : ∀ i, (sets i).Nonempty
  disjoint : Pairwise fun i j => Disjoint (sets i) (sets j)
  on : ∀ q i, F q (flip (fun _ => false) (sets i)) = true











end
end Sensitivity205


/- Local proof component: CoupledArithmetic. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Sensitivity20635




end Sensitivity20635


/- Local proof component: CoupledRepair. -/

open OAI.Paper320 Sensitivity205
open scoped Classical

namespace Sensitivity20635
noncomputable section
set_option maxHeartbeats 3000000

section Geometry
variable {k r h : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin (h+1) → (I → Bool) → Bool)
  (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)

 theorem target_gate_disjoint : Disjoint (targetCandidates T label F q x)
    (gateCandidates T label F q x) := by
  apply Finset.disjoint_left.mpr
  intro i ht hg
  have ht' := (Finset.mem_filter.mp ht).2.1
  have hg' := (Finset.mem_filter.mp hg).2.1
  simp [hg'] at ht'

include hF in
 theorem target_not_to_gate {i j : Fin k}
    (hi : i ∈ targetCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x) : ¬ T.Adj i j := by
  intro hij
  have hz := (gateFailures_empty_iff T label F q x i).mp
    (Finset.mem_filter.mp hi).2.2 j hij
  have ho := hF.accepts_of_le (gateIndex_lt_last q).le
    ((targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hj).2.1 (label i j))
  simp [hz] at ho

include hF in
 theorem gate_to_target {i j : Fin k}
    (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ targetCandidates T label F q x) : T.Adj i j := by
  have hne : i ≠ j := by
    intro hij; subst j
    exact Finset.disjoint_left.mp (target_gate_disjoint T label F q x) hj hi
  rcases T.adj_or_reverse hne with ha | ha
  · exact ha
  · exact False.elim (target_not_to_gate T label F hF q x hj hi ha)

 theorem gate_passes {i j : Fin k}
    (hi : i ∈ gateCandidates T label F q x) (hij : T.Adj i j)
    (hne : j ≠ gateWitness T label F q x i) :
    F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  cases ho : F (gateIndex q) (recursiveChild x j (label i j))
  · rfl
  · exact False.elim (hne (gateWitness_unique T label F q x i hi j hij ho))

include hF in
 theorem target_incoming_label (hr : 0 < r) {i j : Fin k}
    (hj : j ∈ targetCandidates T label F q x)
    (hz : F (gateIndex q) (recursiveChild x j (label i j)) = false) :
    label i j = targetWitness F x hr j := by
  exact targetWitness_unique T label F q x hr j hj (label i j)
    (hF.rejects_of_le (gateIndex_lt_last q).le hz)

include hF in
 theorem target_incoming_zero (hr : 0 < r) {i j : Fin k}
    (hj : j ∈ targetCandidates T label F q x)
    (hz : F (gateIndex q) (recursiveChild x j (label i j)) = false) :
    F (gateIndex q) (recursiveChild x j (targetWitness F x hr j)) = false := by
  rwa [target_incoming_label T label F hF q x hr hj hz] at hz

include hF in
 theorem gate_incoming_unique {i j v : Fin k}
    (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x)
    (hv : v ∈ gateCandidates T label F q x)
    (hiv : T.Adj i v) (hjv : T.Adj j v) : i = j := by
  by_contra hne
  rcases T.adj_or_reverse hne with hij | hji
  · have h1 := gateCandidates_neighbor T label F hF q x i j hi hj hij
    have h2 := gateCandidates_neighbor T label F hF q x i v hi hv hiv
    exact T.ne_of_adj hjv (h1.trans h2.symm)
  · have h1 := gateCandidates_neighbor T label F hF q x j i hj hi hji
    have h2 := gateCandidates_neighbor T label F hF q x j v hj hv hjv
    exact T.ne_of_adj hiv (h1.trans h2.symm)

include hF in
 theorem target_sources_card (hr : 0 < r) :
    ((targetCandidates T label F q x).filter fun i =>
      F (gateIndex q) (recursiveChild x i (targetWitness F x hr i)) = true).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hio⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hjo⟩ := Finset.mem_filter.mp hj
  by_contra hne
  rcases T.adj_or_reverse hne with hij | hji
  · have hz := (gateFailures_empty_iff T label F q x i).mp
      (Finset.mem_filter.mp hi).2.2 j hij
    have hz' := target_incoming_zero T label F hF q x hr hj hz
    simp [hz'] at hjo
  · have hz := (gateFailures_empty_iff T label F q x j).mp
      (Finset.mem_filter.mp hj).2.2 i hji
    have hz' := target_incoming_zero T label F hF q x hr hi hz
    simp [hz'] at hio

include hF in
 theorem gate_internal_forces_targets (hr : 0 < r) {i j : Fin k}
    (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x) (hij : T.Adj i j)
    {v : Fin k} (hv : v ∈ targetCandidates T label F q x) :
    F (gateIndex q) (recursiveChild x v (targetWitness F x hr v)) = false := by
  have hw := gateCandidates_neighbor T label F hF q x i j hi hj hij
  have hvj : v ≠ j := by
    intro e
    exact Finset.disjoint_left.mp (target_gate_disjoint T label F q x) (e ▸ hv) hj
  apply target_incoming_zero T label F hF q x hr hv
  apply gate_passes T label F q x hi (gate_to_target T label F hF q x hi hv)
  rwa [← hw]

include hF in
 theorem gate_card_two_targets_zero (hr : 0 < r)
    (hg : 2 ≤ (gateCandidates T label F q x).card)
    {v : Fin k} (hv : v ∈ targetCandidates T label F q x) :
    F (gateIndex q) (recursiveChild x v (targetWitness F x hr v)) = false := by
  obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp (by omega :
    1 < (gateCandidates T label F q x).card)
  rcases T.adj_or_reverse hne with hij | hji
  · exact gate_internal_forces_targets T label F hF q x hr hi hj hij hv
  · exact gate_internal_forces_targets T label F hF q x hr hj hi hji hv

 theorem gate_targets_false_witness_not_target (hr : 0 < r)
    (hz : ∀ v ∈ targetCandidates T label F q x,
      F (gateIndex q) (recursiveChild x v (targetWitness F x hr v)) = false)
    {i : Fin k} (hi : i ∈ gateCandidates T label F q x)
    (ht : F (Fin.last h) (recursiveChild x (gateWitness T label F q x i)
      (label i (gateWitness T label F q x i))) = false) :
    gateWitness T label F q x i ∉ targetCandidates T label F q x := by
  intro hw
  have he := targetWitness_unique T label F q x hr _ hw _ ht
  have hon := (gateWitness_spec T label F q x i hi).2
  rw [he, hz _ hw] at hon
  exact Bool.false_ne_true hon

include hF in
 theorem gate_false_target_sink {i : Fin k}
    (hi : i ∈ gateCandidates T label F q x)
    (ht : F (Fin.last h) (recursiveChild x (gateWitness T label F q x i)
      (label i (gateWitness T label F q x i))) = false) :
    i ∈ gateSinks T label F q x := by
  apply Finset.mem_filter.mpr
  refine ⟨hi, ?_⟩
  intro j hj hij
  have hw := gateCandidates_neighbor T label F hF q x i j hi hj hij
  have hon := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hj).2.1 (label i j)
  rw [hw, ht] at hon
  exact Bool.false_ne_true hon

include hF in
 theorem gate_false_targets_card :
    ((gateCandidates T label F q x).filter fun i =>
      F (Fin.last h) (recursiveChild x (gateWitness T label F q x i)
        (label i (gateWitness T label F q x i))) = false).card ≤ 1 := by
  apply le_trans (Finset.card_le_card (t := gateSinks T label F q x) ?_)
    (gateSinks_card T label F q x)
  intro i hi
  exact gate_false_target_sink T label F hF q x (Finset.mem_filter.mp hi).1
    (Finset.mem_filter.mp hi).2

include hF in
 theorem gate_sink_card_le_two {v : Fin k}
    (hv : v ∈ gateSinks T label F q x) : (gateCandidates T label F q x).card ≤ 2 := by
  have hvin := (Finset.mem_filter.mp hv).1
  have hout := (Finset.mem_filter.mp hv).2
  have he : ((gateCandidates T label F q x).erase v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := Finset.mem_erase.mp hi
    have hj' := Finset.mem_erase.mp hj
    have hiv : T.Adj i v := (T.adj_or_reverse hi'.1).resolve_right (hout i hi'.2)
    have hjv : T.Adj j v := (T.adj_or_reverse hj'.1).resolve_right (hout j hj'.2)
    exact gate_incoming_unique T label F hF q x hi'.2 hj'.2 hvin hiv hjv
  have hc := Finset.card_erase_add_one hvin
  omega

include hF in
 theorem gate_card_three_witness_mem
    (hg : (gateCandidates T label F q x).card = 3) {i : Fin k}
    (hi : i ∈ gateCandidates T label F q x) :
    gateWitness T label F q x i ∈ gateCandidates T label F q x := by
  apply nonsink_gateWitness_mem T label F hF q x i hi
  intro hs
  have hc := gate_sink_card_le_two T label F hF q x hs
  omega

include hF in
 theorem coherent_targets_gates {t : ℕ} (A : Labeling T r t)
    (heq : A.label = label) (hr : 0 < r) (E : Finset (Fin k))
    (hE : E ⊆ gateCandidates T label F q x)
    (hw : ∀ i ∈ E, gateWitness T label F q x i ∉ targetCandidates T label F q x) :
    (targetCandidates T label F q x).card + E.card < t := by
  let pred : Fin k → Fin k := fun j =>
    if h : ∃ i ∈ E, T.Adj i j then h.choose else j
  let m : Fin k → Fin r := fun j =>
    if j ∈ targetCandidates T label F q x then targetWitness F x hr j else label (pred j) j
  have hc : ((targetCandidates T label F q x) ∪ E).card < t := by
    apply A.coherent_card _ m
    intro i hi j hj hij
    rw [heq]
    rcases Finset.mem_union.mp hj with hj | hj
    · have hz : F (gateIndex q) (recursiveChild x j (label i j)) = false := by
        rcases Finset.mem_union.mp hi with hi | hi
        · exact (gateFailures_empty_iff T label F q x i).mp (Finset.mem_filter.mp hi).2.2 j hij
        · exact gate_passes T label F q x (hE hi) hij (fun e => hw i hi (e ▸ hj))
      simpa [m, hj] using target_incoming_label T label F hF q x hr hj hz
    · have hjn : j ∉ targetCandidates T label F q x := fun h =>
        Finset.disjoint_left.mp (target_gate_disjoint T label F q x) h (hE hj)
      have hie : i ∈ E := by
        rcases Finset.mem_union.mp hi with hi | hi
        · exact False.elim (target_not_to_gate T label F hF q x hi (hE hj) hij)
        · exact hi
      have hex : ∃ a ∈ E, T.Adj a j := ⟨i, hie, hij⟩
      have hp : pred j ∈ E ∧ T.Adj (pred j) j := by
        simp only [pred, dif_pos hex]
        exact hex.choose_spec
      have hip : i = pred j := gate_incoming_unique T label F hF q x
        (hE hie) (hE hp.1) (hE hj) hij hp.2
      simpa [m, hjn, hip]
  rw [Finset.card_union_of_disjoint] at hc
  · exact hc
  · exact (target_gate_disjoint T label F q x).mono_right hE


include hF in
 theorem targets_card_sub_two {t : ℕ} (A : Labeling T r t)
    (heq : A.label = label) (hr : 0 < r)
    (hg : 2 ≤ (gateCandidates T label F q x).card) :
    (targetCandidates T label F q x).card ≤ t-2 := by
  obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp (by omega :
    1 < (gateCandidates T label F q x).card)
  have step : ∀ i ∈ gateCandidates T label F q x, ∀ j ∈ gateCandidates T label F q x,
      T.Adj i j → (targetCandidates T label F q x).card ≤ t-2 := by
    intro a ha b hb hab
    have hc := coherent_targets_gates T label F hF q x A heq hr {a}
      (by simpa using ha) (by
        intro c hc
        have hc' : c = a := Finset.mem_singleton.mp hc
        subst c
        rw [← gateCandidates_neighbor T label F hF q x a b ha hb hab]
        exact fun h => Finset.disjoint_left.mp (target_gate_disjoint T label F q x) h hb)
    simp only [Finset.card_singleton] at hc
    omega
  rcases T.adj_or_reverse hne with hij | hji
  · exact step i hi j hj hij
  · exact step j hj i hi hji

include hF in
 theorem targets_card_with_ordinary {t : ℕ} (A : Labeling T r t)
    (heq : A.label = label) (hr : 0 < r)
    (hg : 2 ≤ (gateCandidates T label F q x).card)
    {b : Fin k} (hb : b ∈ gateCandidates T label F q x)
    (hbo : F (Fin.last h) (recursiveChild x (gateWitness T label F q x b)
      (label b (gateWitness T label F q x b))) = false) :
    (targetCandidates T label F q x).card + (gateCandidates T label F q x).card < t := by
  apply coherent_targets_gates T label F hF q x A heq hr _ (fun _ h => h)
  intro i hi
  by_cases he : i = b
  · subst i
    exact gate_targets_false_witness_not_target T label F q x hr
      (fun v hv => gate_card_two_targets_zero T label F hF q x hr hg hv) hb hbo
  · have hs := (Finset.mem_filter.mp (gate_false_target_sink T label F hF q x hb hbo)).2
    have hib := (T.adj_or_reverse he).resolve_right (hs i hi)
    rw [← gateCandidates_neighbor T label F hF q x i b hi hb hib]
    exact fun h => Finset.disjoint_left.mp (target_gate_disjoint T label F q x) h hb

include hF in
 theorem targets_card_with_three {t : ℕ} (A : Labeling T r t)
    (heq : A.label = label) (hr : 0 < r)
    (hg : (gateCandidates T label F q x).card = 3) :
    (targetCandidates T label F q x).card ≤ t-4 := by
  have hc := coherent_targets_gates T label F hF q x A heq hr
    (gateCandidates T label F q x) (fun _ h => h) (by
      intro i hi ht
      exact Finset.disjoint_left.mp (target_gate_disjoint T label F q x) ht
        (gate_card_three_witness_mem T label F hF q x hg hi))
  omega

end Geometry

section Repair
variable {k r h : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin (h+1) → (I → Bool) → Bool)
  (hF : NestedFamily F) (q q' : Fin h) (hqq : q ≤ q')
  (x : ((Fin k × Fin r) × I) → Bool)




end Repair





end
end Sensitivity20635



end Bundle2075_1

/- Component 2: MixedTargets.lean -/
section Bundle2075_2


/-!
Generalized tournament transfer with independently chosen target predicates.

The counting geometry is reused from the accepted Prove2Me 2.0635 proof.
This file supplies the new cross-target argument. See README.md for provenance.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical

namespace Sensitivity2075
noncomputable section

/-- Package a gate and a target as a two-entry family, so the existing
single-output tournament geometry applies unchanged. -/
def twoPred {n : ℕ} {I : Type} (F : Fin n → (I → Bool) → Bool)
    (G A : Fin n) : Fin 2 → (I → Bool) → Bool :=
  Fin.cases (F G) (fun _ => F A)

theorem twoPred_nested {n : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (G A : Fin n) (hGA : G ≤ A) : NestedFamily (twoPred F G A) := by
  constructor
  intro q q' x hqq hx
  fin_cases q <;> fin_cases q' <;> simp_all [twoPred]
  exact hF.accepts_of_le hGA hx

/-- `mixedFamily T label F A G` uses `F A` for its row targets and `F G`
for its outgoing guards. -/
def mixedFamily {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) : (((Fin k × Fin r) × I) → Bool) → Bool :=
  recursiveFamily T label (twoPred F G A) 0




section CrossTargets
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
  (x : ((Fin k × Fin r) × I) → Bool)

include hF hA hG in
/-- A strong target candidate also fails the weak target at its unique
missing child; otherwise the weak output was already true. -/
theorem target_candidate_weak_false (hr : 0 < r)
    (hx : mixedFamily T label F Ai Gi x = false) {i : Fin k}
    (hi : i ∈ targetCandidates T label (twoPred F Gj Aj) 0 x) :
    F Ai (recursiveChild x i (targetWitness (twoPred F Gj Aj) x hr i)) = false := by
  cases hw : F Ai (recursiveChild x i (targetWitness (twoPred F Gj Aj) x hr i))
  · rfl
  · have hrow : rowClause T label (twoPred F Gi Ai) 0 x i = true := by
      apply (rowClause_eq_true_iff T label (twoPred F Gi Ai) 0 x i).mpr
      constructor
      · intro c
        change F Ai (recursiveChild x i c) = true
        by_cases hc : c = targetWitness (twoPred F Gj Aj) x hr i
        · simpa only [hc] using hw
        · have hs : F Aj (recursiveChild x i c) = true := by
            cases hz : F Aj (recursiveChild x i c)
            · exact False.elim (hc (targetWitness_unique T label
                (twoPred F Gj Aj) 0 x hr i hi c hz))
            · rfl
          exact hF.accepts_of_le hA hs
      · intro j hij
        exact hF.rejects_of_le hG
          ((gateFailures_empty_iff T label (twoPred F Gj Aj) 0 x i).mp
            (Finset.mem_filter.mp hi).2.2 j hij)
    have hz := (recursiveFamily_eq_false_iff T label (twoPred F Gi Ai) 0 x).mp hx i
    simp [hz] at hrow

include hF hA hG in
/-- At a strong guard candidate the weak guard also fails at the unique
failed guard child; all other weak conditions already hold. -/
theorem gate_candidate_weak_true
    (hx : mixedFamily T label F Ai Gi x = false) {i : Fin k}
    (hi : i ∈ gateCandidates T label (twoPred F Gj Aj) 0 x) :
    F Gi (recursiveChild x (gateWitness T label (twoPred F Gj Aj) 0 x i)
      (label i (gateWitness T label (twoPred F Gj Aj) 0 x i))) = true := by
  cases hw : F Gi (recursiveChild x (gateWitness T label (twoPred F Gj Aj) 0 x i)
      (label i (gateWitness T label (twoPred F Gj Aj) 0 x i)))
  · have hrow : rowClause T label (twoPred F Gi Ai) 0 x i = true := by
      apply (rowClause_eq_true_iff T label (twoPred F Gi Ai) 0 x i).mpr
      constructor
      · intro c
        exact hF.accepts_of_le hA
          ((targetFailures_empty_iff (twoPred F Gj Aj) x i).mp
            (Finset.mem_filter.mp hi).2.1 c)
      · intro j hij
        by_cases he : j = gateWitness T label (twoPred F Gj Aj) 0 x i
        · change F Gi (recursiveChild x j (label i j)) = false
          simpa only [he] using hw
        · exact hF.rejects_of_le hG
            (gate_passes T label (twoPred F Gj Aj) 0 x hi hij he)
    have hz := (recursiveFamily_eq_false_iff T label (twoPred F Gi Ai) 0 x).mp hx i
    simp [hz] at hrow
  · rfl

end CrossTargets











end
end Sensitivity2075


end Bundle2075_2

/- Component 3: H1Combinatorics.lean -/
section Bundle2075_3


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical BigOperators

namespace Sensitivity2075
noncomputable section













end
end Sensitivity2075

end Bundle2075_3

/- Component 4: H1Definitions.lean -/
section Bundle2075_4


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical BigOperators

namespace Sensitivity2075
noncomputable section

def missingTargets {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin r) :=
  Finset.univ.filter fun c => F A (recursiveChild x i c) = false

def failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun j => T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true

def tolerantRow {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Bool :=
  decide ((∀ c, F A (recursiveChild x i c) = true) ∧
    (failedGuards T label F G x i).card ≤ q)

def tolerantFamily {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) : Bool :=
  decide (∃ i, tolerantRow T label F A G q x i = true)

def tolerantTargets {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => (missingTargets F A x i).card = 1 ∧
    (failedGuards T label F G x i).card ≤ q

def tolerantGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => missingTargets F A x i = ∅ ∧
    (failedGuards T label F G x i).card = q+1

@[simp] theorem mem_missingTargets {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) (c : Fin r) :
    c ∈ missingTargets F A x i ↔ F A (recursiveChild x i c) = false := by
  simp [missingTargets]

@[simp] theorem mem_failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) :
    j ∈ failedGuards T label F G x i ↔
      T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true := by
  simp [failedGuards]

theorem missingTargets_empty {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    missingTargets F A x i = ∅ ↔ ∀ c, F A (recursiveChild x i c) = true := by
  simp [missingTargets, Finset.filter_eq_empty_iff]

theorem tolerantRow_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    tolerantRow T label F A G q x i = true ↔
      (∀ c, F A (recursiveChild x i c) = true) ∧
      (failedGuards T label F G x i).card ≤ q := by
  simp only [tolerantRow, decide_eq_true_eq]

theorem tolerantFamily_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantFamily T label F A G q x = true ↔
      ∃ i, tolerantRow T label F A G q x i = true := by
  simp only [tolerantFamily, decide_eq_true_eq]

theorem tolerantFamily_false {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantFamily T label F A G q x = false ↔
      ∀ i, tolerantRow T label F A G q x i = false := by
  simp [tolerantFamily]

section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

theorem guard_mem_flip_iff {v : Fin k} (hne : (v, label i v) ≠ (j,c)) :
    v ∈ failedGuards T label F G (flip x {((j,c),a)}) i ↔
      v ∈ failedGuards T label F G x i := by
  simp only [mem_failedGuards, recursiveChild_flip_other x j v c (label i v) a hne]

theorem guards_flip_subset :
    failedGuards T label F G (flip x {((j,c),a)}) i ⊆
      insert j (failedGuards T label F G x i) := by
  intro v hv
  by_cases he : v = j
  · exact Finset.mem_insert.mpr (Or.inl he)
  · exact Finset.mem_insert.mpr (Or.inr
      ((guard_mem_flip_iff T label F G x i j c a (by
        intro hh; exact he (congrArg Prod.fst hh))).mp hv))

theorem guards_subset_flip :
    failedGuards T label F G x i ⊆
      insert j (failedGuards T label F G (flip x {((j,c),a)}) i) := by
  intro v hv
  by_cases he : v = j
  · exact Finset.mem_insert.mpr (Or.inl he)
  · exact Finset.mem_insert.mpr (Or.inr
      ((guard_mem_flip_iff T label F G x i j c a (by
        intro hh; exact he (congrArg Prod.fst hh))).mpr hv))

theorem guards_flip_card_le :
    (failedGuards T label F G (flip x {((j,c),a)}) i).card ≤
      (failedGuards T label F G x i).card + 1 :=
  (Finset.card_le_card (guards_flip_subset T label F G x i j c a)).trans
    (Finset.card_insert_le _ _)

theorem guards_card_le_flip :
    (failedGuards T label F G x i).card ≤
      (failedGuards T label F G (flip x {((j,c),a)}) i).card + 1 :=
  (Finset.card_le_card (guards_subset_flip T label F G x i j c a)).trans
    (Finset.card_insert_le _ _)

theorem guards_flip_own :
    failedGuards T label F G (flip x {((i,c),a)}) i =
      failedGuards T label F G x i := by
  ext v
  by_cases hv : T.Adj i v
  · exact guard_mem_flip_iff T label F G x i i c a (by
      intro hh; exact T.ne_of_adj hv (congrArg Prod.fst hh).symm)
  · simp only [mem_failedGuards, hv, false_and]

/-- A strict decrease in guard count identifies a guard changing true to false. -/
theorem guard_decrease_location
    (hdec : (failedGuards T label F G (flip x {((j,c),a)}) i).card <
      (failedGuards T label F G x i).card) :
    T.Adj i j ∧ c = label i j ∧ F G (recursiveChild x j c) = true ∧
      F G (flip (recursiveChild x j c) {a}) = false := by
  obtain ⟨v, hv, hv'⟩ := Finset.exists_mem_notMem_of_card_lt_card hdec
  have hloc : (v, label i v) = (j,c) := by
    by_contra hh
    exact hv' ((guard_mem_flip_iff T label F G x i j c a hh).mpr hv)
  have hvj : v = j := congrArg Prod.fst hloc
  subst v
  have hcl : c = label i j := (congrArg Prod.snd hloc).symm
  subst c
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F G x i j).mp hv
  refine ⟨hij, rfl, hon, ?_⟩
  have hoff : F G (recursiveChild (flip x {((j,label i j),a)}) j (label i j)) = false := by
    simpa only [mem_failedGuards, hij, true_and, Bool.not_eq_true] using hv'
  simpa only [recursiveChild_flip_same] using hoff

/-- A strict increase identifies a guard changing false to true. -/
theorem guard_increase_location
    (hinc : (failedGuards T label F G x i).card <
      (failedGuards T label F G (flip x {((j,c),a)}) i).card) :
    T.Adj i j ∧ c = label i j ∧ F G (recursiveChild x j c) = false ∧
      F G (flip (recursiveChild x j c) {a}) = true := by
  obtain ⟨v, hv', hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hinc
  have hloc : (v, label i v) = (j,c) := by
    by_contra hh
    exact hv ((guard_mem_flip_iff T label F G x i j c a hh).mp hv')
  have hvj : v = j := congrArg Prod.fst hloc
  subst v
  have hcl : c = label i j := (congrArg Prod.snd hloc).symm
  subst c
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F G _ i j).mp hv'
  refine ⟨hij, rfl, ?_, ?_⟩
  · simpa only [mem_failedGuards, hij, true_and, Bool.not_eq_true] using hv
  · simpa only [recursiveChild_flip_same] using hon

end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

/-- A successful repair either fills the unique missing target or removes one
of exactly `q+1` failed guards from an already active row. -/
theorem tolerant_repair_cases
    (hoff : tolerantRow T label F A G q x i = false)
    (hon : tolerantRow T label F A G q (flip x {((j,c),a)}) i = true) :
    (i ∈ tolerantTargets T label F A G q x ∧ j = i ∧
      F A (recursiveChild x j c) = false ∧
      F A (flip (recursiveChild x j c) {a}) = true) ∨
    (i ∈ tolerantGuards T label F A G q x ∧ T.Adj i j ∧ c = label i j ∧
      F G (recursiveChild x j c) = true ∧
      F G (flip (recursiveChild x j c) {a}) = false) := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F A G q _ i).mp hon
  by_cases hji : j = i
  · subst j
    rw [guards_flip_own] at hg
    have hton : F A (flip (recursiveChild x i c) {a}) = true := by
      simpa only [recursiveChild_flip_same] using ht c
    have hother : ∀ d, d ≠ c → F A (recursiveChild x i d) = true := by
      intro d hdc
      simpa only [recursiveChild_flip_other x i i c d a (by
        intro he; exact hdc (congrArg Prod.snd he))] using ht d
    have htoff : F A (recursiveChild x i c) = false := by
      cases hc : F A (recursiveChild x i c)
      · rfl
      · have hrow := (tolerantRow_true T label F A G q x i).mpr ⟨?_, hg⟩
        · simp [hoff] at hrow
        · intro d
          by_cases hd : d = c
          · simpa only [hd] using hc
          · exact hother d hd
    have hmissing : missingTargets F A x i = {c} := by
      ext d
      simp only [mem_missingTargets, Finset.mem_singleton]
      constructor
      · intro hd
        by_contra hne
        have hh := hother d hne
        simp [hd] at hh
      · rintro rfl
        exact htoff
    exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hmissing], hg⟩,
      rfl, htoff, hton⟩
  · have htargets : ∀ d, F A (recursiveChild x i d) = true := by
      intro d
      simpa only [recursiveChild_flip_other x j i c d a (by
        intro he; exact hji (congrArg Prod.fst he).symm)] using ht d
    have hcount : q < (failedGuards T label F G x i).card := by
      by_contra hn
      have hh := (tolerantRow_true T label F A G q x i).mpr
        ⟨htargets, by omega⟩
      simp [hoff] at hh
    have hupper := guards_card_le_flip T label F G x i j c a
    have hexact : (failedGuards T label F G x i).card = q+1 := by omega
    have hl := guard_decrease_location T label F G x i j c a (by omega)
    exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (missingTargets_empty F A x i).mpr htargets, hexact⟩, hl⟩

/-- Destroying an accepting row either loses a target or increases its guard
count from exactly `q` to `q+1`. -/
theorem tolerant_loss_cases
    (hon : tolerantRow T label F A G q x i = true)
    (hoff : tolerantRow T label F A G q (flip x {((j,c),a)}) i = false) :
    (j = i ∧ F A (recursiveChild x j c) = true ∧
      F A (flip (recursiveChild x j c) {a}) = false) ∨
    ((failedGuards T label F G x i).card = q ∧ T.Adj i j ∧ c = label i j ∧
      F G (recursiveChild x j c) = false ∧
      F G (flip (recursiveChild x j c) {a}) = true) := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F A G q x i).mp hon
  by_cases hji : j = i
  · subst j
    refine Or.inl ⟨rfl, ht c, ?_⟩
    cases hc : F A (flip (recursiveChild x i c) {a})
    · rfl
    · have hg' : (failedGuards T label F G (flip x {((i,c),a)}) i).card ≤ q := by
        simpa only [guards_flip_own] using hg
      have hh := (tolerantRow_true T label F A G q _ i).mpr ⟨?_, hg'⟩
      · simp [hoff] at hh
      · intro d
        by_cases hd : d = c
        · subst d
          simpa only [recursiveChild_flip_same] using hc
        · simpa only [recursiveChild_flip_other x i i c d a (by
            intro he; exact hd (congrArg Prod.snd he))] using ht d
  · have htargets : ∀ d, F A (recursiveChild (flip x {((j,c),a)}) i d) = true := by
      intro d
      simpa only [recursiveChild_flip_other x j i c d a (by
        intro he; exact hji (congrArg Prod.fst he).symm)] using ht d
    have hcount : q < (failedGuards T label F G (flip x {((j,c),a)}) i).card := by
      by_contra hn
      have hh := (tolerantRow_true T label F A G q _ i).mpr
        ⟨htargets, by omega⟩
      simp [hoff] at hh
    have hupper := guards_flip_card_le T label F G x i j c a
    have hexact : (failedGuards T label F G x i).card = q := by omega
    exact Or.inr ⟨hexact, guard_increase_location T label F G x i j c a (by omega)⟩

end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)

include hF in
theorem failedGuards_subset {Gi Gj : Fin n} (hG : Gj ≤ Gi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    failedGuards T label F Gi x i ⊆ failedGuards T label F Gj x i := by
  intro j hj
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F Gi x i j).mp hj
  exact (mem_failedGuards T label F Gj x i j).mpr ⟨hij, hF.accepts_of_le hG hon⟩

include hF in
theorem tolerantRow_nested {Ai Aj Gi Gj : Fin n} {qi qj : ℕ}
    (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hq : qj ≤ qi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : tolerantRow T label F Aj Gj qj x i = true) :
    tolerantRow T label F Ai Gi qi x i = true := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F Aj Gj qj x i).mp hi
  exact (tolerantRow_true T label F Ai Gi qi x i).mpr
    ⟨fun c => hF.accepts_of_le hA (ht c),
      (Finset.card_le_card (failedGuards_subset T label F hF hG x i)).trans (hg.trans hq)⟩

end Nesting

end
end Sensitivity2075

end Bundle2075_4

/- Component 5: H1Candidates.lean -/
section Bundle2075_5


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical BigOperators

namespace Sensitivity2075
noncomputable section

def missingWitness {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k) : Fin r :=
  if h : (missingTargets F A x i).Nonempty then h.choose else ⟨0, hr⟩

theorem missing_singleton {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) :
    missingTargets F A x i = {missingWitness F A x hr i} := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hi
  have hne : (missingTargets F A x i).Nonempty := hc ▸ Finset.singleton_nonempty c
  have hm : missingWitness F A x hr i ∈ missingTargets F A x i := by
    simp only [missingWitness, dif_pos hne]
    exact hne.choose_spec
  rw [hc, Finset.mem_singleton] at hm
  simpa only [hm] using hc

theorem missingWitness_false {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) :
    F A (recursiveChild x i (missingWitness F A x hr i)) = false := by
  apply (mem_missingTargets F A x i _).mp
  rw [missing_singleton F A x hr i hi]
  exact Finset.mem_singleton_self _

theorem missingWitness_unique {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) (c : Fin r)
    (hc : F A (recursiveChild x i c) = false) : c = missingWitness F A x hr i := by
  have hm := (mem_missingTargets F A x i c).mpr hc
  rwa [missing_singleton F A x hr i hi, Finset.mem_singleton] at hm

theorem missingWitness_other_true {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) (c : Fin r)
    (hc : c ≠ missingWitness F A x hr i) : F A (recursiveChild x i c) = true := by
  cases hh : F A (recursiveChild x i c)
  · exact False.elim (hc (missingWitness_unique F A x hr i hi c hh))
  · rfl







section JointCandidates
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
  (x : ((Fin k × Fin r) × I) → Bool)

include hF hA hG in
/-- The unique missing strong target must also fail the weak target. -/
theorem tolerant_target_weak_false {qi qj : ℕ} (hq : qj ≤ qi) (hr : 0 < r)
    (hx : tolerantFamily T label F Ai Gi qi x = false) {i : Fin k}
    (hi : i ∈ tolerantTargets T label F Aj Gj qj x) :
    F Ai (recursiveChild x i (missingWitness F Aj x hr i)) = false := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  cases hw : F Ai (recursiveChild x i (missingWitness F Aj x hr i))
  · rfl
  · have hrow : tolerantRow T label F Ai Gi qi x i = true := by
      apply (tolerantRow_true T label F Ai Gi qi x i).mpr
      constructor
      · intro c
        by_cases hc : c = missingWitness F Aj x hr i
        · simpa only [hc] using hw
        · exact hF.accepts_of_le hA (missingWitness_other_true F Aj x hr i hmiss c hc)
      · exact (Finset.card_le_card (failedGuards_subset T label F hF hG x i)).trans
          (hguards.trans hq)
    have hoff := (tolerantFamily_false T label F Ai Gi qi x).mp hx i
    simp [hoff] at hrow

include hF hA hG in
/-- At a common-zero guard candidate of equal tolerance, the weak and strong
failed-guard sets coincide. -/
theorem tolerant_guard_sets_eq (q : ℕ)
    (hx : tolerantFamily T label F Ai Gi q x = false) {i : Fin k}
    (hi : i ∈ tolerantGuards T label F Aj Gj q x) :
    failedGuards T label F Gi x i = failedGuards T label F Gj x i := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  have htargets : ∀ c, F Ai (recursiveChild x i c) = true :=
    fun c => hF.accepts_of_le hA ((missingTargets_empty F Aj x i).mp hmiss c)
  have hcount : q < (failedGuards T label F Gi x i).card := by
    by_contra hn
    have hrow := (tolerantRow_true T label F Ai Gi q x i).mpr ⟨htargets, by omega⟩
    have hoff := (tolerantFamily_false T label F Ai Gi q x).mp hx i
    simp [hoff] at hrow
  exact Finset.eq_of_subset_of_card_le (failedGuards_subset T label F hF hG x i) (by omega)

include hF hA hG in
/-- A guard candidate for the stricter tolerance already accepts the weaker
output. Hence no such candidate occurs at a common zero input. -/
theorem no_guard_candidate_of_strict {qi qj : ℕ} (hq : qj < qi)
    (hx : tolerantFamily T label F Ai Gi qi x = false) {i : Fin k}
    (hi : i ∈ tolerantGuards T label F Aj Gj qj x) : False := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  have hrow : tolerantRow T label F Ai Gi qi x i = true := by
    apply (tolerantRow_true T label F Ai Gi qi x i).mpr
    refine ⟨fun c => hF.accepts_of_le hA ((missingTargets_empty F Aj x i).mp hmiss c), ?_⟩
    have hh := Finset.card_le_card (failedGuards_subset T label F hF hG x i)
    omega
  have hoff := (tolerantFamily_false T label F Ai Gi qi x).mp hx i
  simp [hoff] at hrow

end JointCandidates




end
end Sensitivity2075

end Bundle2075_5

/- Component 6: H1Zero.lean -/
section Bundle2075_6


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical BigOperators

namespace Sensitivity2075
noncomputable section




end
end Sensitivity2075

end Bundle2075_6

/- Component 7: H1One.lean -/
section Bundle2075_7


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical BigOperators

namespace Sensitivity2075
noncomputable section

/-- One-side joint transfer for any equal tolerance. In particular, H1 pays
`o-1` passing guards instead of the ordinary construction's `o`. -/
theorem tolerant_pair_one {n k r : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F) (o q : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (Z Y : Fin n → Fin n → ℕ) (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T label F Ai Gi q x = true)
    (hx' : tolerantFamily T label F Aj Gj q x = true) :
    jointSensitivityAt (tolerantFamily T label F Ai Gi q)
      (tolerantFamily T label F Aj Gj q) x ≤ r*Y Ai Aj+(o-q)*Z Gj Gi := by
  obtain ⟨i, hi'⟩ := (tolerantFamily_true T label F Aj Gj q x).mp hx'
  have hi := tolerantRow_nested T label F hF hA hG (le_refl q) x i hi'
  have hw := (tolerantRow_true T label F Ai Gi q x i).mp hi
  have hs := (tolerantRow_true T label F Aj Gj q x i).mp hi'
  let B := failedGuards T label F Gi x i
  let P := if B.card = q then (Finset.univ.filter (T.Adj i)) \ B else ∅
  let U := Finset.univ.biUnion fun c => childJointChanges F Ai Aj x i c
  let V := P.biUnion fun j => childJointChanges F Gj Gi x j (label i j)
  have hPcard : P.card ≤ o-q := by
    by_cases he : B.card = q
    · have hsub : B ⊆ Finset.univ.filter (T.Adj i) := by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ((mem_failedGuards T label F Gi x i j).mp hj).1⟩
      simp only [P, if_pos he, Finset.card_sdiff_of_subset hsub, ho i, he, le_refl]
    · simp only [P, if_neg he, Finset.card_empty, Nat.zero_le]
  have hPfalse : ∀ j ∈ P,
      F Gj (recursiveChild x j (label i j)) = false ∧
      F Gi (recursiveChild x j (label i j)) = false := by
    intro j hj
    by_cases he : B.card = q
    · have hh : j ∈ (Finset.univ.filter (T.Adj i)) \ B := by simpa only [P, if_pos he] using hj
      obtain ⟨hj, hjB⟩ := Finset.mem_sdiff.mp hh
      have hij := (Finset.mem_filter.mp hj).2
      have hset : B = failedGuards T label F Gj x i :=
        Finset.eq_of_subset_of_card_le (failedGuards_subset T label F hF hG x i) (by
          change (failedGuards T label F Gj x i).card ≤ B.card
          rw [he]
          exact hs.2)
      have hsnot : j ∉ failedGuards T label F Gj x i := by rw [← hset]; exact hjB
      constructor
      · simpa only [mem_failedGuards, hij, true_and, Bool.not_eq_true] using hsnot
      · simpa only [B, mem_failedGuards, hij, true_and, Bool.not_eq_true] using hjB
    · simp only [P, if_neg he, Finset.notMem_empty] at hj
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T label F Ai Gi q (flip x {p}) ≠ tolerantFamily T label F Ai Gi q x ∧
      tolerantFamily T label F Aj Gj q (flip x {p}) ≠ tolerantFamily T label F Aj Gj q x) ⊆
      U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hf : tolerantFamily T label F Ai Gi q (flip x {((j,c),a)}) = false := by
      cases hy : tolerantFamily T label F Ai Gi q (flip x {((j,c),a)})
      · rfl
      · exact False.elim (hc.1 (hy.trans hx.symm))
    have hf' : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)}) = false := by
      cases hy : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)})
      · rfl
      · exact False.elim (hc.2 (hy.trans hx'.symm))
    have hif := (tolerantFamily_false T label F Ai Gi q _).mp hf i
    have hif' := (tolerantFamily_false T label F Aj Gj q _).mp hf' i
    rcases tolerant_loss_cases T label F Ai Gi q x i j c a hi hif with
      ⟨hji, hwon, hwoff⟩ | ⟨hcount, hij, hcl, hwoff, hwon⟩
    · rcases tolerant_loss_cases T label F Aj Gj q x i j c a hi' hif' with
        ⟨_, hson, hsoff⟩ | ⟨_, hij, _⟩
      · subst j
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨c, Finset.mem_univ _, ?_⟩
        have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
            F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
          simp [hwon, hwoff, hson, hsoff]
        simpa [childJointChanges] using hn
      · exact False.elim (T.ne_of_adj hij hji.symm)
    · rcases tolerant_loss_cases T label F Aj Gj q x i j c a hi' hif' with
        ⟨hji, _⟩ | ⟨_, _, _, hsoff, hson⟩
      · exact False.elim (T.ne_of_adj hij hji.symm)
      · subst c
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨j, ?_, ?_⟩
        · change j ∈ P
          simp only [P, show B.card = q from hcount, if_pos rfl]
          apply Finset.mem_sdiff.mpr
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, by
            simp only [B, mem_failedGuards, hwoff, Bool.false_eq_true, and_false, not_false_eq_true]⟩
        · have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
                F Gj (recursiveChild x j (label i j)) ∧
              F Gi (flip (recursiveChild x j (label i j)) {a}) ≠
                F Gi (recursiveChild x j (label i j)) := by
              simp [hwon, hwoff, hson, hsoff]
          simpa [childJointChanges] using hn
  have hU : U.card ≤ r*Y Ai Aj := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childJointChanges F Ai Aj x i c) (Y Ai Aj) (fun c _ => by
        rw [childJointChanges_card]
        exact hY _ _ hA _ (hw.1 c) (hs.1 c))
  have hV : V.card ≤ (o-q)*Z Gj Gi := by
    have hh : V.card ≤ P.card * Z Gj Gi := by
      apply card_biUnion_le_mul
      intro j hj
      rw [childJointChanges_card]
      exact hZ _ _ hG _ (hPfalse j hj).1 (hPfalse j hj).2
    exact hh.trans (Nat.mul_le_mul_right _ hPcard)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le U V).trans (Nat.add_le_add hU hV))

end
end Sensitivity2075

end Bundle2075_7

/- Component 8: H1Strict.lean -/
section Bundle2075_8


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical BigOperators

namespace Sensitivity2075
noncomputable section

/-- Strictly larger tolerance removes all guard flips from the joint one side. -/
theorem strict_tolerance_pair_one {n k r : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (Y : Fin n → Fin n → ℕ) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
    (qi qj : ℕ) (hq : qj < qi)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T label F Ai Gi qi x = true)
    (hx' : tolerantFamily T label F Aj Gj qj x = true) :
    jointSensitivityAt (tolerantFamily T label F Ai Gi qi)
      (tolerantFamily T label F Aj Gj qj) x ≤ r*Y Ai Aj := by
  obtain ⟨i, hi'⟩ := (tolerantFamily_true T label F Aj Gj qj x).mp hx'
  have hi := tolerantRow_nested T label F hF hA hG hq.le x i hi'
  have hw := (tolerantRow_true T label F Ai Gi qi x i).mp hi
  have hs := (tolerantRow_true T label F Aj Gj qj x i).mp hi'
  let U := Finset.univ.biUnion fun c => childJointChanges F Ai Aj x i c
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T label F Ai Gi qi (flip x {p}) ≠ tolerantFamily T label F Ai Gi qi x ∧
      tolerantFamily T label F Aj Gj qj (flip x {p}) ≠ tolerantFamily T label F Aj Gj qj x) ⊆ U := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hf : tolerantFamily T label F Ai Gi qi (flip x {((j,c),a)}) = false := by
      cases hy : tolerantFamily T label F Ai Gi qi (flip x {((j,c),a)})
      · rfl
      · exact False.elim (hc.1 (hy.trans hx.symm))
    have hif := (tolerantFamily_false T label F Ai Gi qi _).mp hf i
    rcases tolerant_loss_cases T label F Ai Gi qi x i j c a hi hif with
      ⟨hji, hwon, hwoff⟩ | ⟨hcount, _⟩
    · subst j
      have hson := hs.1 c
      have hsoff := hF.rejects_of_le hA hwoff
      apply Finset.mem_biUnion.mpr
      refine ⟨c, Finset.mem_univ _, ?_⟩
      have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
          F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
        simp [hwon, hwoff, hson, hsoff]
      simpa [childJointChanges] using hn
    · have hb := Finset.card_le_card (failedGuards_subset T label F hF hG x i)
      omega
  have hU : U.card ≤ r*Y Ai Aj := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childJointChanges F Ai Aj x i c) (Y Ai Aj) (fun c _ => by
        rw [childJointChanges_card]
        exact hY _ _ hA _ (hw.1 c) (hs.1 c))
  exact (Finset.card_le_card hsub).trans hU

/-- Tolerance zero is precisely the task-1 tournament construction. -/
theorem tolerant_zero_eq_mixed {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool) (A G : Fin n) :
    tolerantFamily T label F A G 0 = mixedFamily T label F A G := by
  funext x
  simp only [tolerantFamily, mixedFamily, recursiveFamily]
  congr 1
  apply propext
  simp only [tolerantRow_true, rowClause_eq_true_iff, Nat.le_zero, Finset.card_eq_zero,
    failedGuards, Finset.filter_eq_empty_iff]
  simp [twoPred, gateIndex]
  rfl

theorem tolerantTargets_zero {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantTargets T label F A G 0 x = targetCandidates T label (twoPred F G A) 0 x := by
  ext i
  simp only [tolerantTargets, targetCandidates, Finset.mem_filter, Finset.mem_univ,
    true_and, Nat.le_zero, Finset.card_eq_zero]
  rfl

/-- The source/source-free target charge at tolerance zero. -/
theorem strict_zero_arithmetic (n0 n1 t a b : ℕ) (hn1 : n1 ≤ 1)
    (hn : n0+n1 ≤ t-1) :
    n1*a+n0*b ≤ max (a+(t-2)*b) ((t-1)*b) := by
  interval_cases n1
  · have hh := Nat.mul_le_mul_right b hn
    simp only [Nat.add_zero, Nat.zero_mul, Nat.zero_add] at *
    exact hh.trans (le_max_right _ _)
  · have hh : n0 ≤ t-2 := by omega
    have hm := Nat.mul_le_mul_right b hh
    exact (show 1*a+n0*b ≤ a+(t-2)*b by omega).trans (le_max_left _ _)

/-- H1 (or any positive tolerance) versus an ordinary strong output: only
target repairs survive, with at most one source paying the larger joint cost. -/
theorem strict_ordinary_pair_zero {n k r t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T r t)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (Z : Fin n → Fin n → ℕ) (hZ : PairBound F false Z)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hGA : Gi ≤ Ai)
    (q : ℕ) (hq : 0 < q)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T L.label F Ai Gi q x = false)
    (hx' : tolerantFamily T L.label F Aj Gj 0 x = false) :
    jointSensitivityAt (tolerantFamily T L.label F Ai Gi q)
      (tolerantFamily T L.label F Aj Gj 0) x ≤
      max (Z Ai Aj+(t-2)*Z Gj Aj) ((t-1)*Z Gj Aj) := by
  let S := twoPred F Gj Aj
  let TC := tolerantTargets T L.label F Aj Gj 0 x
  let tw := missingWitness F Aj x hr
  let T0 := TC.filter fun i => F Gj (recursiveChild x i (tw i)) = false
  let T1 := TC.filter fun i => F Gj (recursiveChild x i (tw i)) = true
  let U := T1.biUnion fun i => childJointChanges F Ai Aj x i (tw i)
  let V := T0.biUnion fun i => childJointChanges F Gj Aj x i (tw i)
  have hGJA : Gj ≤ Aj := hG.trans (hGA.trans hA)
  have hS : NestedFamily S := twoPred_nested F hF Gj Aj hGJA
  have htw : ∀ i, tw i = targetWitness S x hr i := by intro i; rfl
  have hTC : TC = targetCandidates T L.label S 0 x := tolerantTargets_zero T L.label F Aj Gj x
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T L.label F Ai Gi q (flip x {p}) ≠ tolerantFamily T L.label F Ai Gi q x ∧
      tolerantFamily T L.label F Aj Gj 0 (flip x {p}) ≠ tolerantFamily T L.label F Aj Gj 0 x) ⊆
      U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T L.label F Aj Gj 0 (flip x {((j,c),a)}) = true := by
      cases hy : tolerantFamily T L.label F Aj Gj 0 (flip x {((j,c),a)})
      · exact False.elim (hc.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi⟩ := (tolerantFamily_true T L.label F Aj Gj 0 _).mp hon
    have hoff := (tolerantFamily_false T L.label F Aj Gj 0 x).mp hx' i
    rcases tolerant_repair_cases T L.label F Aj Gj 0 x i j c a hoff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, _⟩
    · subst j
      have hcw := missingWitness_unique F Aj x hr i (Finset.mem_filter.mp hit).2.1 c htoff
      have hwo : F Ai (recursiveChild x i c) = false := by
        rw [hcw]
        exact tolerant_target_weak_false T L.label F hF Ai Aj Gi Gj hA hG x
          (Nat.zero_le q) hr hx hit
      have hwn := hF.accepts_of_le hA hton
      have hgn := hF.accepts_of_le hGJA hton
      cases hgo : F Gj (recursiveChild x i c)
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hgo
        · have hn : F Gj (flip (recursiveChild x i c) {a}) ≠ F Gj (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
            simp [hgo, hgn, htoff, hton]
          simpa [childJointChanges, tw, hcw] using hn
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hgo
        · have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
            simp [hwo, hwn, htoff, hton]
          simpa [childJointChanges, tw, hcw] using hn
    · exact False.elim (no_guard_candidate_of_strict T L.label F hF Ai Aj Gi Gj hA hG x hq hx hig)
  have hU : U.card ≤ T1.card*Z Ai Aj := by
    apply card_biUnion_le_mul
    intro i hi
    have hit := (Finset.mem_filter.mp hi).1
    rw [childJointChanges_card]
    exact hZ _ _ hA _
      (tolerant_target_weak_false T L.label F hF Ai Aj Gi Gj hA hG x (Nat.zero_le q) hr hx hit)
      (missingWitness_false F Aj x hr i (Finset.mem_filter.mp hit).2.1)
  have hV : V.card ≤ T0.card*Z Gj Aj := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hit, hgo⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hZ _ _ hGJA _ hgo (missingWitness_false F Aj x hr i (Finset.mem_filter.mp hit).2.1)
  have hnsum : T0.card+T1.card = TC.card := by
    simpa [T0, T1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := TC)
        (fun i => F Gj (recursiveChild x i (tw i)) = false))
  have hn1 : T1.card ≤ 1 := by
    have hh := target_sources_card T L.label S hS 0 x hr
    change ((targetCandidates T L.label S 0 x).filter fun i =>
      F Gj (recursiveChild x i (targetWitness S x hr i)) = true).card ≤ 1 at hh
    simpa only [T1, hTC, htw] using hh
  have hn : T0.card+T1.card ≤ t-1 := by
    have hh := Sensitivity205.targetCandidates_card T L S hS 0 x hr
    rw [← hTC] at hh
    omega
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  change jointSensitivityAt _ _ x ≤ _ at hh
  exact (hh.trans (Nat.add_le_add hU hV)).trans
    (strict_zero_arithmetic T0.card T1.card t (Z Ai Aj) (Z Gj Aj) hn1 hn)

end
end Sensitivity2075

end Bundle2075_8

/- Component 9: H1Transfer.lean -/
section Bundle2075_9


/-!
H1 transfer package for task 2 of the 2.075 formalization.

For H1/H1 pairs this proves
  Z' ≤ 3*(t-1)*Z(Ai,Aj) + 3*Y(Gj,Gi) + 7*Y(Gj,Aj),
  Y' ≤ r*Y(Ai,Aj) + (o-1)*Z(Gj,Gi).
For H1/H0 pairs it proves
  Z' ≤ max (Z(Ai,Aj)+(t-2)*Z(Gj,Aj)) ((t-1)*Z(Gj,Aj)),
  Y' ≤ r*Y(Ai,Aj).

Here r is the row width (2 in the certificate), o is the common outdegree,
and t is the ordinary coherent-labeling threshold. No defective-labeling
existence theorem is assumed. All candidate counts are proved from the
ordinary labeling bound.
-/


end Bundle2075_9

/- Component 10: Auxiliary.lean -/
section Bundle2075_10


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped BigOperators

namespace Sensitivity2075
noncomputable section

/-- The three auxiliary rows: OR, first coordinate, AND. -/
def auxInner (s : Fin 3) (y : Fin 2 → Bool) : Bool :=
  if s = 0 then y 0 || y 1 else if s = 1 then y 0 else y 0 && y 1

def auxCost (s t : Fin 3) (b : Bool) : ℕ :=
  if s = 0 ∧ t = 2 then 0 else
  if b then (if s = 2 then 2 else 1) else (if t = 0 then 2 else 1)

def flip2 (y : Fin 2 → Bool) (c : Fin 2) : Fin 2 → Bool :=
  fun d => if d = c then !(y d) else y d

theorem flip_eq2 (y : Fin 2 → Bool) (c : Fin 2) : OAI.Paper320.flip y {c} = flip2 y c := by
  funext d
  simp [OAI.Paper320.flip, flip2]

theorem auxInner_table : ∀ (s t : Fin 3) (y z : Fin 2 → Bool), s ≤ t →
    (∀ c, z c = true → y c = true) →
    (auxInner t z = true → auxInner s y = true) ∧
    ∀ b, auxInner s y = b → auxInner t z = b →
      (Finset.univ.filter fun c => auxInner s (flip y {c}) ≠ auxInner s y ∧
        auxInner t (flip z {c}) ≠ auxInner t z).card ≤ auxCost s t b ∧
      ∀ c, auxInner s (flip y {c}) ≠ auxInner s y →
        auxInner t (flip z {c}) ≠ auxInner t z → y c = b ∧ z c = b := by
  simp_rw [flip_eq2]
  intro s t y z
  fin_cases s <;> fin_cases t <;>
    cases hy0 : y 0 <;> cases hy1 : y 1 <;>
    cases hz0 : z 0 <;> cases hz1 : z 1 <;>
    simp [auxInner, auxCost, flip2, Fin.forall_fin_two, hy0, hy1, hz0, hz1, Finset.univ_fin2]
  all_goals decide

theorem auxInner_all_true (s : Fin 3) : auxInner s (fun _ => true) = true := by
  fin_cases s <;> rfl
theorem auxInner_all_false (s : Fin 3) : auxInner s (fun _ => false) = false := by
  fin_cases s <;> rfl


theorem auxInner_zero_false (y : Fin 2 → Bool)
    (h : auxInner 0 y = false) : ∀ c, y c = false := by
  simp [auxInner, Bool.or_eq_false_iff] at h
  intro c
  fin_cases c
  · exact h.1
  · exact h.2

open scoped Classical

def auxRow {n k : ℕ} {I : Type} (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) (i : Fin k) : Bool :=
  auxInner s (fun c => F A (recursiveChild x i c))

def auxFamily {n k : ℕ} {I : Type} (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) : Bool :=
  decide (∃ i, auxRow s F A x i = true)

theorem auxFamily_true {n k : ℕ} {I : Type} (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    auxFamily s F A x = true ↔ ∃ i, auxRow s F A x i = true := by
  simp [auxFamily]
theorem auxFamily_false {n k : ℕ} {I : Type} (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    auxFamily s F A x = false ↔ ∀ i, auxRow s F A x i = false := by
  simp [auxFamily]

theorem auxRow_nested {n k : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    {s t : Fin 3} {A B : Fin n} (hst : s ≤ t) (hAB : A ≤ B)
    (x : ((Fin k × Fin 2) × I) → Bool) (i : Fin k)
    (hi : auxRow t F B x i = true) : auxRow s F A x i = true :=
  (auxInner_table s t _ _ hst (fun _ => hF.accepts_of_le hAB)).1 hi

theorem auxRow_flip_other {n k : ℕ} {I : Type} (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) (i j : Fin k) (c : Fin 2) (a : I)
    (hij : i ≠ j) :
    auxRow s F A (flip x {((j,c),a)}) i = auxRow s F A x i := by
  unfold auxRow
  congr 1
  funext d
  rw [recursiveChild_flip_other x j i c d a (by
    intro hh; exact hij (congrArg Prod.fst hh))]

theorem auxRow_flip_change {n k : ℕ} {I : Type} (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) (i j : Fin k) (c : Fin 2) (a : I)
    (hc : auxRow s F A (flip x {((j,c),a)}) i ≠ auxRow s F A x i) :
    j = i ∧ F A (flip (recursiveChild x i c) {a}) ≠ F A (recursiveChild x i c) ∧
      auxInner s (flip (fun d => F A (recursiveChild x i d)) {c}) ≠ auxRow s F A x i := by
  have hji : j = i := by
    by_contra hn
    exact hc (auxRow_flip_other s F A x i j c a (Ne.symm hn))
  subst j
  have hn : F A (flip (recursiveChild x i c) {a}) ≠ F A (recursiveChild x i c) := by
    intro he
    apply hc
    unfold auxRow
    congr 1
    funext d
    by_cases hd : d = c
    · subst d; simpa only [recursiveChild_flip_same] using he
    · rw [recursiveChild_flip_other x i i c d a (by
        intro hh; exact hd (congrArg Prod.snd hh))]
  refine ⟨rfl, hn, ?_⟩
  have he : (fun d => F A (recursiveChild (flip x {((i,c),a)}) i d)) =
      flip (fun d => F A (recursiveChild x i d)) {c} := by
    funext d
    by_cases hd : d = c
    · subst d
      rw [recursiveChild_flip_same]
      simp only [OAI.Paper320.flip, Finset.mem_singleton, if_pos rfl]
      cases h0 : F A (recursiveChild x i c) <;>
        cases h1 : F A (flip (recursiveChild x i c) {a}) <;> simp_all
    · rw [recursiveChild_flip_other x i i c d a (by
        intro hh; exact hd (congrArg Prod.snd hh))]
      simp [OAI.Paper320.flip, hd]
  simpa only [auxRow, he] using hc

def jointChanges {J : Type} [Fintype J] (f g : (J → Bool) → Bool) (x : J → Bool) :=
  Finset.univ.filter fun a => f (flip x {a}) ≠ f x ∧ g (flip x {a}) ≠ g x

theorem auxRow_pair_bound {n k : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (s t : Fin 3) (hst : s ≤ t) (A B : Fin n) (hAB : A ≤ B)
    (b : Bool) (V : Fin n → Fin n → ℕ) (hV : PairBound F b V)
    (x : ((Fin k × Fin 2) × I) → Bool) (i : Fin k)
    (hx : auxRow s F A x i = b) (hx' : auxRow t F B x i = b) :
    (jointChanges (fun z => auxRow s F A z i) (fun z => auxRow t F B z i) x).card ≤
      auxCost s t b * V A B := by
  let y := fun c => F A (recursiveChild x i c)
  let z := fun c => F B (recursiveChild x i c)
  let C := Finset.univ.filter fun c => auxInner s (flip y {c}) ≠ auxInner s y ∧
    auxInner t (flip z {c}) ≠ auxInner t z
  have ht := (auxInner_table s t y z hst (fun _ => hF.accepts_of_le hAB)).2 b hx hx'
  have hsub : jointChanges (fun z => auxRow s F A z i) (fun z => auxRow t F B z i) x ⊆
      C.biUnion (fun c => childJointChanges F A B x i c) := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hh := (Finset.mem_filter.mp hp).2
    obtain ⟨hji, ha, hia⟩ := auxRow_flip_change s F A x i j c a hh.1
    subst j
    obtain ⟨_, hb, hib⟩ := auxRow_flip_change t F B x i i c a hh.2
    apply Finset.mem_biUnion.mpr
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hia, hib⟩,
      by simpa [childJointChanges] using And.intro ha hb⟩
  calc
    _ ≤ (C.biUnion (fun c => childJointChanges F A B x i c)).card := Finset.card_le_card hsub
    _ ≤ C.card * V A B := card_biUnion_le_mul _ _ _ (by
      intro c hc
      have hh := (Finset.mem_filter.mp hc).2
      have hv := ht.2 c hh.1 hh.2
      rw [childJointChanges_card]
      exact hV A B hAB _ hv.1 hv.2)
    _ ≤ _ := Nat.mul_le_mul_right _ ht.1

theorem aux_pair_zero {n k : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (s t : Fin 3) (hst : s ≤ t) (A B : Fin n) (hAB : A ≤ B)
    (Z : Fin n → Fin n → ℕ) (hZ : PairBound F false Z)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : auxFamily s F A x = false) (hx' : auxFamily t F B x = false) :
    jointSensitivityAt (auxFamily s F A) (auxFamily t F B) x ≤
      k * (auxCost s t false * Z A B) := by
  let C := fun i => jointChanges (fun z => auxRow s F A z i) (fun z => auxRow t F B z i) x
  have hw := (auxFamily_false s F A x).mp hx
  have hs := (auxFamily_false t F B x).mp hx'
  have hsub : jointChanges (auxFamily s F A) (auxFamily t F B) x ⊆
      Finset.univ.biUnion C := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hh := (Finset.mem_filter.mp hp).2
    have hl (v : Fin 3) (Q : Fin n) (hoff : ∀ i, auxRow v F Q x i = false)
        (hon : auxFamily v F Q (flip x {((j,c),a)}) = true) :
        auxRow v F Q (flip x {((j,c),a)}) j = true := by
      obtain ⟨i, hi⟩ := (auxFamily_true v F Q _).mp hon
      by_cases hij : i = j
      · simpa only [hij] using hi
      · rw [auxRow_flip_other v F Q x i j c a hij, hoff i] at hi
        contradiction
    have ha : auxFamily s F A (flip x {((j,c),a)}) = true := by
      simpa only [hx, Bool.not_eq_false] using hh.1
    have hb : auxFamily t F B (flip x {((j,c),a)}) = true := by
      simpa only [hx', Bool.not_eq_false] using hh.2
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hl s A hw ha, hw j],
        by simp [hl t B hs hb, hs j]⟩⟩
  exact (Finset.card_le_card hsub).trans (by
    simpa using card_biUnion_le_mul Finset.univ C (auxCost s t false * Z A B)
      (fun i _ => auxRow_pair_bound F hF s t hst A B hAB false Z hZ x i (hw i) (hs i)))

theorem aux_pair_one {n k : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (s t : Fin 3) (hst : s ≤ t) (A B : Fin n) (hAB : A ≤ B)
    (Y : Fin n → Fin n → ℕ) (hY : PairBound F true Y)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : auxFamily s F A x = true) (hx' : auxFamily t F B x = true) :
    jointSensitivityAt (auxFamily s F A) (auxFamily t F B) x ≤ auxCost s t true * Y A B := by
  obtain ⟨i, hi⟩ := (auxFamily_true t F B x).mp hx'
  have hwi := auxRow_nested F hF hst hAB x i hi
  have hsub : jointChanges (auxFamily s F A) (auxFamily t F B) x ⊆
      jointChanges (fun z => auxRow s F A z i) (fun z => auxRow t F B z i) x := by
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2
    have ha : auxFamily s F A (flip x {p}) = false := by
      simpa only [hx, Bool.not_eq_true] using hh.1
    have hb : auxFamily t F B (flip x {p}) = false := by
      simpa only [hx', Bool.not_eq_true] using hh.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simp [(auxFamily_false s F A _).mp ha i, hwi],
      by simp [(auxFamily_false t F B _).mp hb i, hi]⟩
  exact (Finset.card_le_card hsub).trans
    (auxRow_pair_bound F hF s t hst A B hAB true Y hY x i hwi hi)

end
end Sensitivity2075

end Bundle2075_10

/- Component 11: AuxTournament.lean -/
section Bundle2075_11


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical BigOperators
namespace Sensitivity2075
noncomputable section

theorem aux_of_all_targets {n k : ℕ} {I : Type} (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A B : Fin n) (hAB : A ≤ B) (x : ((Fin k × Fin 2) × I) → Bool)
    (i : Fin k) (hi : ∀ c, F B (recursiveChild x i c) = true) :
    auxFamily s F A x = true := by
  apply (auxFamily_true s F A x).mpr
  refine ⟨i, ?_⟩
  change auxInner s (fun c => F A (recursiveChild x i c)) = true
  have he : (fun c => F A (recursiveChild x i c)) = fun _ => true :=
    funext (fun c => hF.accepts_of_le hAB (hi c))
  rw [he, auxInner_all_true]

theorem aux_target_false {n k : ℕ} {I : Type} (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A B : Fin n) (hAB : A ≤ B) (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : auxFamily s F A x = false) (i : Fin k)
    (hc : (missingTargets F B x i).card = 1) :
    F A (recursiveChild x i (missingWitness F B x (by decide) i)) = false := by
  cases hw : F A (recursiveChild x i (missingWitness F B x (by decide) i))
  · rfl
  · have hon : auxFamily s F A x = true := by
      apply aux_of_all_targets s F hF A A le_rfl x i
      intro c
      by_cases he : c = missingWitness F B x (by decide) i
      · simpa only [he] using hw
      · exact hF.accepts_of_le hAB (missingWitness_other_true F B x (by decide) i hc c he)
    simp [hx] at hon

theorem aux_target_repair {n k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A B G : Fin n) (hAB : A ≤ B) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : auxFamily s F A x = false)
    (hx' : tolerantFamily T label F B G q x = false)
    (j : Fin k) (c : Fin 2) (a : I)
    (hon : tolerantFamily T label F B G q (flip x {((j,c),a)}) = true) :
    j ∈ tolerantTargets T label F B G q x ∧
      c = missingWitness F B x (by decide) j ∧
      F A (recursiveChild x j c) = false ∧ F B (recursiveChild x j c) = false ∧
      F B (flip (recursiveChild x j c) {a}) = true := by
  obtain ⟨i, hi⟩ := (tolerantFamily_true T label F B G q _).mp hon
  have hoff := (tolerantFamily_false T label F B G q x).mp hx' i
  rcases tolerant_repair_cases T label F B G q x i j c a hoff hi with
    ⟨hit, hji, hbo, hbn⟩ | ⟨hig, _⟩
  · subst j
    have hm := (Finset.mem_filter.mp hit).2.1
    have he := missingWitness_unique F B x (by decide) i hm c hbo
    refine ⟨hit, he, ?_, hbo, hbn⟩
    rw [he]
    exact aux_target_false s F hF A B hAB x hx i hm
  · have ht := (missingTargets_empty F B x i).mp (Finset.mem_filter.mp hig).2.1
    have hh := aux_of_all_targets s F hF A B hAB x i ht
    simp [hx] at hh




theorem aux_u_winner_zero {n k : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A B G : Fin n) (hAB : A ≤ B) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : auxFamily 0 F A x = false)
    (hx' : tolerantFamily T label F B G q x = false) :
    jointSensitivityAt (auxFamily 0 F A) (tolerantFamily T label F B G q) x ≤ 0 := by
  apply Nat.le_zero.mpr
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨⟨j,c⟩,a⟩ hp
  have hh := (Finset.mem_filter.mp hp).2
  have hon : tolerantFamily T label F B G q (flip x {((j,c),a)}) = true := by
    simpa only [hx', Bool.not_eq_false] using hh.2
  obtain ⟨hit, he, _, _, _⟩ := aux_target_repair T label 0 F hF A B G hAB q x hx hx' j c a hon
  have hw := auxInner_zero_false _ ((auxFamily_false 0 F A x).mp hx j)
  have hn : (Fin.rev c : Fin 2) ≠ c := by fin_cases c <;> decide
  have ht := missingWitness_other_true F B x (by decide) j
    (Finset.mem_filter.mp hit).2.1 (Fin.rev c) (by simpa only [← he] using hn)
  have ht' := hF.accepts_of_le hAB ht
  simp [hw] at ht'

theorem aux_winner_one {n k : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin 2) (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A B G : Fin n) (hAB : A ≤ B) (q : ℕ)
    (Y : Fin n → Fin n → ℕ) (hY : PairBound F true Y)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : auxFamily s F A x = true)
    (hx' : tolerantFamily T label F B G q x = true) :
    jointSensitivityAt (auxFamily s F A) (tolerantFamily T label F B G q) x ≤
      auxCost s 2 true * Y A B := by
  obtain ⟨i,hi⟩ := (tolerantFamily_true T label F B G q x).mp hx'
  have ht := (tolerantRow_true T label F B G q x i).mp hi
  have hs2 : s ≤ (2 : Fin 3) := by omega
  have hbi : auxRow 2 F B x i = true := by
    change auxInner 2 (fun c => F B (recursiveChild x i c)) = true
    rw [show (fun c => F B (recursiveChild x i c)) = (fun _ => true) from funext ht.1]
    rfl
  have hai := auxRow_nested F hF hs2 hAB x i hbi
  have hsub : jointChanges (auxFamily s F A) (tolerantFamily T label F B G q) x ⊆
      jointChanges (fun z => auxRow s F A z i) (fun z => auxRow 2 F B z i) x := by
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2
    have ha : auxFamily s F A (flip x {p}) = false := by
      simpa only [hx, Bool.not_eq_true] using hc.1
    have haf := (auxFamily_false s F A _).mp ha i
    have hbf : auxRow 2 F B (flip x {p}) i = false := by
      cases he : auxRow 2 F B (flip x {p}) i
      · rfl
      · have hh := auxRow_nested F hF hs2 hAB (flip x {p}) i he
        simp [haf] at hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [haf,hai], by simp [hbf,hbi]⟩
  exact (Finset.card_le_card hsub).trans
    (auxRow_pair_bound F hF s 2 hs2 A B hAB true Y hY x i hai hbi)

end
end Sensitivity2075

end Bundle2075_11

/- Component 12: AuxOrdinary.lean -/
section Bundle2075_12


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical BigOperators
namespace Sensitivity2075
noncomputable section

theorem aux_ordinary_zero {n k t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T 2 t) (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A B G : Fin n) (hAB : A ≤ B) (hGB : G ≤ B)
    (Z : Fin n → Fin n → ℕ) (hZ : PairBound F false Z)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : auxFamily s F A x = false)
    (hx' : tolerantFamily T L.label F B G 0 x = false) :
    jointSensitivityAt (auxFamily s F A) (tolerantFamily T L.label F B G 0) x ≤
      max (Z A B+(t-2)*Z (min A G) B) ((t-1)*Z (min A G) B) := by
  let S := twoPred F G B
  let TC := tolerantTargets T L.label F B G 0 x
  let tw := missingWitness F B x (by decide)
  let T0 := TC.filter fun i => F G (recursiveChild x i (tw i)) = false
  let T1 := TC.filter fun i => F G (recursiveChild x i (tw i)) = true
  let U := T1.biUnion fun i => childJointChanges F A B x i (tw i)
  let V := T0.biUnion fun i => childJointChanges F (min A G) B x i (tw i)
  have hGJA : G ≤ B := hGB
  have hS : NestedFamily S := twoPred_nested F hF G B hGJA
  have htw : ∀ i, tw i = targetWitness S x (by decide) i := by intro i; rfl
  have hTC : TC = targetCandidates T L.label S 0 x := tolerantTargets_zero T L.label F B G x
  have hlow (i : Fin k) (hi : i ∈ T0) : F (min A G) (recursiveChild x i (tw i)) = false := by
    obtain ⟨hit, hgo⟩ := Finset.mem_filter.mp hi
    have hao := aux_target_false s F hF A B hAB x hx i (Finset.mem_filter.mp hit).2.1
    rcases le_total A G with hag | hga
    · simpa only [min_eq_left hag] using hao
    · simpa only [min_eq_right hga] using hgo
  have hminB : min A G ≤ B := (min_le_left _ _).trans hAB
  have hsub : jointChanges (auxFamily s F A) (tolerantFamily T L.label F B G 0) x ⊆ U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T L.label F B G 0 (flip x {((j,c),a)}) = true := by
      simpa only [hx', Bool.not_eq_false] using hc.2
    obtain ⟨hit, he, hao, hbo, hbn⟩ := aux_target_repair T L.label s F hF A B G hAB 0 x hx hx' j c a hon
    have han := hF.accepts_of_le hAB hbn
    cases hgo : F G (recursiveChild x j c)
    · have ht0 : j ∈ T0 := Finset.mem_filter.mpr ⟨hit, by simpa only [tw, ← he] using hgo⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j, ht0, ?_⟩
      have hlo : F (min A G) (recursiveChild x j c) = false := by simpa only [tw, ← he] using hlow j ht0
      have hln := hF.accepts_of_le hminB hbn
      have hn : F (min A G) (flip (recursiveChild x j c) {a}) ≠ F (min A G) (recursiveChild x j c) ∧
          F B (flip (recursiveChild x j c) {a}) ≠ F B (recursiveChild x j c) := by simp [hlo,hln,hbo,hbn]
      simpa [childJointChanges,tw,he] using hn
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨hit, by simpa only [tw, ← he] using hgo⟩, ?_⟩
      have hn : F A (flip (recursiveChild x j c) {a}) ≠ F A (recursiveChild x j c) ∧
          F B (flip (recursiveChild x j c) {a}) ≠ F B (recursiveChild x j c) := by simp [hao,han,hbo,hbn]
      simpa [childJointChanges,tw,he] using hn
  have hU : U.card ≤ T1.card*Z A B := by
    apply card_biUnion_le_mul
    intro i hi
    have hit := (Finset.mem_filter.mp hi).1
    rw [childJointChanges_card]
    exact hZ _ _ hAB _
      (aux_target_false s F hF A B hAB x hx i (Finset.mem_filter.mp hit).2.1)
      (missingWitness_false F B x (by decide) i (Finset.mem_filter.mp hit).2.1)
  have hV : V.card ≤ T0.card*Z (min A G) B := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hit, hgo⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hZ _ _ hminB _ (hlow i hi) (missingWitness_false F B x (by decide) i (Finset.mem_filter.mp hit).2.1)
  have hnsum : T0.card+T1.card = TC.card := by
    simpa [T0, T1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := TC)
        (fun i => F G (recursiveChild x i (tw i)) = false))
  have hn1 : T1.card ≤ 1 := by
    have hh := target_sources_card T L.label S hS 0 x (by decide)
    change ((targetCandidates T L.label S 0 x).filter fun i =>
      F G (recursiveChild x i (targetWitness S x (by decide) i)) = true).card ≤ 1 at hh
    simpa only [T1, hTC, htw] using hh
  have hn : T0.card+T1.card ≤ t-1 := by
    have hh := Sensitivity205.targetCandidates_card T L S hS 0 x (by decide)
    rw [← hTC] at hh
    omega
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  change jointSensitivityAt _ _ x ≤ _ at hh
  exact (hh.trans (Nat.add_le_add hU hV)).trans
    (strict_zero_arithmetic T0.card T1.card t (Z A B) (Z (min A G) B) hn1 hn)

end
end Sensitivity2075

end Bundle2075_12

/- Component 13: ProfileContainment.lean -/
section Bundle2075_13


set_option autoImplicit false
open OAI.Paper320 Sensitivity205
open scoped Classical
namespace Sensitivity2075
noncomputable section

theorem joint_interval_subset {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (i j a b : Fin n) (hia : i ≤ a) (hab : a ≤ b) (hbj : b ≤ j)
    (v : Bool) (x : I → Bool) (hi : F i x = v) (hj : F j x = v) :
    F a x = v ∧ F b x = v ∧
    jointChanges (F i) (F j) x ⊆ jointChanges (F a) (F b) x := by
  have hv (q : Fin n) (hiq : i ≤ q) (hqj : q ≤ j) : F q x = v := by
    cases v
    · exact hF.rejects_of_le hiq hi
    · exact hF.accepts_of_le hqj hj
  have ha := hv a hia (hab.trans hbj)
  have hb := hv b (hia.trans hab) hbj
  refine ⟨ha, hb, ?_⟩
  intro p hp
  have hh := (Finset.mem_filter.mp hp).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · cases v
    · have hon : F j (flip x {p}) = true := by simpa [hj] using hh.2
      simp [ha, hF.accepts_of_le (hab.trans hbj) hon]
    · have hoff : F i (flip x {p}) = false := by simpa [hi] using hh.1
      simp [ha, hF.rejects_of_le hia hoff]
  · cases v
    · have hon : F j (flip x {p}) = true := by simpa [hj] using hh.2
      simp [hb, hF.accepts_of_le hbj hon]
    · have hoff : F i (flip x {p}) = false := by simpa [hi] using hh.1
      simp [hb, hF.rejects_of_le (hia.trans hab) hoff]

theorem pairBound_containment {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (v : Bool) (R V : Fin n → Fin n → ℕ) (hR : PairBound F v R)
    (hw : ∀ i j, i ≤ j → ∃ a b, i ≤ a ∧ a ≤ b ∧ b ≤ j ∧ R a b ≤ V i j) :
    PairBound F v V := by
  intro i j hij x hi hj
  obtain ⟨a,b,hia,hab,hbj,hr⟩ := hw i j hij
  obtain ⟨ha,hb,hs⟩ := joint_interval_subset F hF i j a b hia hab hbj v x hi hj
  exact (Finset.card_le_card hs).trans ((hR a b hab x ha hb).trans hr)

end
end Sensitivity2075

end Bundle2075_13

/- Component 14: Stage.lean -/
section Bundle2075_14


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
open OAI.Paper320 Sensitivity205 Sensitivity20635
open scoped Classical BigOperators
namespace Sensitivity2075
noncomputable section

structure Recipe where
  target : Fin 9 → Fin 9
  gate : Fin 9 → Fin 9
  aux : Fin 9 → Fin 3
  tol : Fin 9 → Fin 2































end
end Sensitivity2075

end Bundle2075_14

/- Component 15: BinomialLabeling.lean -/
section Bundle2075_15

set_option autoImplicit false
set_option maxHeartbeats 5000000
/- Local proof component: BinomialLabeling. -/

/-! A finite union bound over subsets, rather than ordered vertex tuples.
The argument is adapted from the accepted public 2.0391 proof.
-/

open OAI.Paper320
open scoped Classical BigOperators

namespace Sensitivity205
noncomputable section




end
end Sensitivity205

namespace Sensitivity20635
noncomputable section








end
end Sensitivity20635

end Bundle2075_15

/- Component 18: BlockAssembly.lean -/
section Bundle2075_18


set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
open OAI.Paper320 Sensitivity205
open scoped Classical BigOperators
namespace Sensitivity2075
noncomputable section







end
end Sensitivity2075

end Bundle2075_18

/- Bundled unchanged module: GenericNQStage -/

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators

namespace SensitivityNQ
noncomputable section

structure Recipe (n : ℕ) where
  target : Fin n → Fin n
  gate : Fin n → Fin n
  aux : Fin n → Fin 3
  tol : Fin n → ℕ

variable {n : ℕ}

def Recipe.Valid (C : Recipe n) : Prop :=
  Monotone C.target ∧
  (∀ i j, i ≤ j → j.val < 3 → C.aux i ≤ C.aux j) ∧
  (∀ i j, i ≤ j → 3 ≤ i.val →
    C.gate j ≤ C.gate i ∧ C.tol j ≤ C.tol i ∧ C.gate i ≤ C.target i)

def stage {k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (C : Recipe n)
    (F : Fin n → (I → Bool) → Bool) (i : Fin n) :
    (((Fin k × Fin 2) × I) → Bool) → Bool :=
  if i.val < 3 then auxFamily (C.aux i) F (C.target i)
  else tolerantFamily T label F (C.target i) (C.gate i) (C.tol i)

theorem stage_nested {k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (C : Recipe n) (hC : C.Valid)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F) :
    NestedFamily (stage T label C F) := by
  constructor
  intro i j x hij hx
  have hA := hC.1 hij
  by_cases hj : j.val < 3
  · have hi : i.val < 3 := by omega
    simp only [stage, if_pos hi, if_pos hj] at hx ⊢
    obtain ⟨v,hv⟩ := (auxFamily_true _ _ _ _).mp hx
    exact (auxFamily_true _ _ _ _).mpr ⟨v,
      auxRow_nested F hF (hC.2.1 i j hij hj) hA x v hv⟩
  · simp only [stage, if_neg hj] at hx
    obtain ⟨v,hv⟩ := (tolerantFamily_true _ _ _ _ _ _ _).mp hx
    by_cases hi : i.val < 3
    · simp only [stage, if_pos hi]
      exact aux_of_all_targets (C.aux i) F hF _ _ hA x v
        ((tolerantRow_true _ _ _ _ _ _ _ _).mp hv).1
    · have hh := hC.2.2 i j hij (by omega)
      simp only [stage, if_neg hi]
      exact (tolerantFamily_true _ _ _ _ _ _ _).mpr ⟨v,
        tolerantRow_nested T label F hF hA hh.1 hh.2.1 x v hv⟩

def rawOne (h : ℕ) (C : Recipe n) (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  if j.val < 3 then auxCost (C.aux i) (C.aux j) true*Y (C.target i) (C.target j)
  else if i.val < 3 then auxCost (C.aux i) 2 true*Y (C.target i) (C.target j)
  else 2*Y (C.target i) (C.target j) +
    if C.tol i = C.tol j then (h-(C.tol j))*Z (C.gate j) (C.gate i) else 0

def Compatible (C : Recipe n) (Z Y : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j, i ≤ j → 3 ≤ i.val →
    Z (C.gate j) (C.target j) ≤ Z (C.target i) (C.target j) ∧
    Y (C.gate j) (C.target j) ≤ Y (C.gate j) (C.gate i)

theorem stage_one {k : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin 2) (h : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = h)
    (C : Recipe n) (hC : C.Valid)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (Z Y : Fin n → Fin n → ℕ) (hZ : PairBound F false Z) (hY : PairBound F true Y) :
    PairBound (stage T label C F) true (rawOne h C Z Y) := by
  intro i j hij x hx hx'
  have hA := hC.1 hij
  by_cases hj : j.val < 3
  · have hi : i.val < 3 := by omega
    simp only [stage, if_pos hi, if_pos hj] at hx hx' ⊢
    simpa only [ite_true, ite_false, Nat.one_ne_zero, rawOne, if_pos hj] using
      aux_pair_one F hF (C.aux i) (C.aux j) (hC.2.1 i j hij hj) _ _ hA Y hY x hx hx'
  · simp only [stage, if_neg hj] at hx'
    by_cases hi : i.val < 3
    · simp only [stage, if_pos hi, if_neg hj] at hx ⊢
      simpa only [ite_true, ite_false, Nat.one_ne_zero, rawOne, if_neg hj, if_pos hi] using
        aux_winner_one T label (C.aux i) F hF _ _ _ hA _ Y hY x hx hx'
    · simp only [stage, if_neg hi, if_neg hj] at hx ⊢
      have hh := hC.2.2 i j hij (by omega)
      by_cases he : C.tol i = C.tol j
      · simpa only [ite_true, ite_false, Nat.one_ne_zero, rawOne, if_neg hj, if_neg hi, if_pos he, he] using
          tolerant_pair_one T label F hF h (C.tol j) ho Z Y hZ hY
            (C.target i) (C.target j) (C.gate i) (C.gate j) hA hh.1 x
            (by simpa only [he] using hx) hx'
      · have hq : C.tol j < C.tol i := by have := hh.2.1; omega
        simpa only [ite_true, ite_false, Nat.one_ne_zero, rawOne, if_neg hj, if_neg hi, if_neg he, Nat.add_zero] using
          strict_tolerance_pair_one T label F hF Y hY
            (C.target i) (C.target j) (C.gate i) (C.gate j) hA hh.1 _ _ hq x hx hx'

theorem rawOne_mul (h : ℕ) (C : Recipe n) (Z Y : Fin n → Fin n → ℕ) (u : ℕ) (i j : Fin n) :
    rawOne h C (fun i j => Z i j*u) (fun i j => Y i j*u) i j = rawOne h C Z Y i j*u := by
  simp only [rawOne]
  split_ifs <;> simp only [Nat.add_mul, Nat.mul_assoc, Nat.zero_mul]


theorem stage_zero_input {k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (C : Recipe n)
    (F : Fin n → (I → Bool) → Bool) (hzero : ∀ q, F q (fun _ => false) = false)
    (q : Fin n) : stage T label C F q (fun _ => false) = false := by
  unfold stage
  split_ifs
  · apply (auxFamily_false _ _ _ _).mpr
    intro i
    change auxInner (C.aux q) (fun _ => F (C.target q) (fun _ => false)) = false
    rw [hzero]
    exact auxInner_all_false _
  · apply (tolerantFamily_false _ _ _ _ _ _ _).mpr
    intro i
    cases he : tolerantRow T label F (C.target q) (C.gate q) (C.tol q) (fun _ => false) i
    · rfl
    · have ht := ((tolerantRow_true _ _ _ _ _ _ _ _).mp he).1 0
      change F (C.target q) (fun _ => false) = true at ht
      rw [hzero] at ht
      contradiction

theorem stage_rowLift {k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (C : Recipe n)
    (F : Fin n → (I → Bool) → Bool) (hzero : ∀ q, F q (fun _ => false) = false)
    (B : Finset I) (hB : ∀ q, F q (flip (fun _ => false) B) = true)
    (i : Fin k) (q : Fin n) :
    stage T label C F q (flip (fun _ => false) (rowLift i B)) = true := by
  unfold stage
  split_ifs
  · apply (auxFamily_true _ _ _ _).mpr
    refine ⟨i, ?_⟩
    simp only [auxRow, recursiveChild_rowLift_same, hB, auxInner_all_true]
  · apply (tolerantFamily_true _ _ _ _ _ _ _).mpr
    refine ⟨i, (tolerantRow_true _ _ _ _ _ _ _ _).mpr ⟨?_, ?_⟩⟩
    · intro c
      rw [recursiveChild_rowLift_same]
      exact hB _
    · have he : failedGuards T label F (C.gate q)
          (flip (fun _ => false) (rowLift i B)) i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        obtain ⟨hij, hon⟩ := (mem_failedGuards _ _ _ _ _ _ _).mp hj
        rw [recursiveChild_rowLift_other _ _ _ _ (T.ne_of_adj hij).symm, hzero] at hon
        contradiction
      rw [he, Finset.card_empty]
      exact Nat.zero_le _


end
end SensitivityNQ

/- Bundled unchanged module: GenericGuardCharge -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators

namespace SensitivityQ
noncomputable section

def DefectBound {k r : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (q s : ℕ) : Prop :=
  ∀ (S : Finset (Fin k)) (m : Fin k → Fin r),
    (∀ i ∈ S, (S.filter fun j => T.Adj i j ∧ label i j ≠ m j).card ≤ q) →
    S.card < s







theorem card_bound_arithmetic (m q : ℕ) (hc : m.choose 2 ≤ m * (q+1)) :
    m ≤ 2*q+3 := by
  have hd : m * (m-1) ≤ 2*(m*(q+1))+1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have hm : 2*q+4 ≤ m := by omega
  have hs : 2*q+3 ≤ m-1 := by omega
  have hmul := Nat.mul_le_mul_left m hs
  nlinarith

/-- The maximum size of a set of almost-passing rows, for arbitrary tolerance. -/
theorem guards_card {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    (tolerantGuards T label F A G q x).card ≤ 2*q+3 := by
  let GC := tolerantGuards T label F A G q x
  have hlocal : ∀ i ∈ GC, (GC.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have hsub : GC.filter (T.Adj i) ⊆ failedGuards T label F G x i := by
      intro j hj
      obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
      exact (mem_failedGuards T label F G x i j).mpr ⟨hij,
        hF.accepts_of_le hGA ((missingTargets_empty F A x j).mp
          (Finset.mem_filter.mp hj).2.1 _)⟩
    have hc := Finset.card_le_card hsub
    have he := (Finset.mem_filter.mp hi).2.2
    omega
  apply card_bound_arithmetic
  calc
    GC.card.choose 2 = ∑ i ∈ GC, (GC.filter (T.Adj i)).card := by
      rw [T.sum_outdegree_eq, T.card_internalEdges]
    _ ≤ ∑ _i ∈ GC, (q+1) := Finset.sum_le_sum hlocal
    _ = GC.card * (q+1) := by simp

/-- Exact weighted charge. Internal tournament arcs have the stronger cost e;
all remaining failed guards have cost c. This formula is valid for every q. -/
theorem guard_charge {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (c e : ℕ) :
    let GC := tolerantGuards T label F A G q x
    (∑ i ∈ GC, ∑ j ∈ failedGuards T label F G x i,
      if j ∈ GC then e else c) =
      (GC.card*(q+1)-GC.card.choose 2)*c + GC.card.choose 2*e := by
  let GC := tolerantGuards T label F A G q x
  let B := failedGuards T label F G x
  have hinside : ∀ i, (B i).filter (fun j => j ∈ GC) = GC.filter (T.Adj i) := by
    intro i
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hb, hj⟩
      exact ⟨hj, ((mem_failedGuards T label F G x i j).mp hb).1⟩
    · rintro ⟨hj, hij⟩
      exact ⟨(mem_failedGuards T label F G x i j).mpr ⟨hij,
        hF.accepts_of_le hGA ((missingTargets_empty F A x j).mp
          (Finset.mem_filter.mp hj).2.1 _)⟩, hj⟩
  have htotal : (∑ i ∈ GC, (B i).card) = GC.card*(q+1) := by
    calc
      _ = ∑ _i ∈ GC, (q+1) := Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2.2)
      _ = _ := by simp
  have hin : (∑ i ∈ GC, ((B i).filter fun j => j ∈ GC).card) = GC.card.choose 2 := by
    simp only [hinside]
    rw [T.sum_outdegree_eq, T.card_internalEdges]
  have hout : (∑ i ∈ GC, ((B i).filter fun j => j ∉ GC).card) =
      GC.card*(q+1)-GC.card.choose 2 := by
    have hh : (∑ i ∈ GC, ((B i).filter fun j => j ∈ GC).card) +
        (∑ i ∈ GC, ((B i).filter fun j => j ∉ GC).card) = GC.card*(q+1) := by
      rw [← Finset.sum_add_distrib, ← htotal]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.card_filter_add_card_filter_not (s := B i) (fun j => j ∈ GC)
    omega
  change (∑ i ∈ GC, ∑ j ∈ B i, if j ∈ GC then e else c) =
    (GC.card*(q+1)-GC.card.choose 2)*c + GC.card.choose 2*e
  calc
    _ = ∑ i ∈ GC, (((B i).filter fun j => j ∈ GC).card*e +
        ((B i).filter fun j => j ∉ GC).card*c) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hin, hout]
      omega







end
end SensitivityQ

/- Bundled unchanged module: GenericZero -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators
namespace SensitivityQ
noncomputable section

theorem targets_card {n k r q v : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (hDefect : DefectBound T label q v) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (tolerantTargets T label F A G q x).card ≤ v-1 := by
  have hc : (tolerantTargets T label F A G q x).card < v := by
    apply hDefect _ (missingWitness F A x hr)
    intro i hi
    have hsub : ((tolerantTargets T label F A G q x).filter fun j =>
        T.Adj i j ∧ label i j ≠ missingWitness F A x hr j) ⊆
        failedGuards T label F G x i := by
      intro j hj
      obtain ⟨hj, hij, hcol⟩ := Finset.mem_filter.mp hj
      apply (mem_failedGuards T label F G x i j).mpr
      exact ⟨hij, hF.accepts_of_le hGA
        (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hj).2.1 _ hcol)⟩
    exact (Finset.card_le_card hsub).trans (Finset.mem_filter.mp hi).2.2

  omega















end
end SensitivityQ

/- Bundled unchanged module: GenericTargetSplitCore -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators
namespace SensitivityQ
noncomputable section

/-- The large-charge target sources have a completely accepting gate row. -/
def positiveTargets {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    Finset (Fin k) :=
  (tolerantTargets T label F A G q x).filter fun i =>
    F G (recursiveChild x i (missingWitness F A x hr i)) = true

theorem source_card_arithmetic (m q : ℕ) (hc : m.choose 2 ≤ m*q) :
    m ≤ 2*q+1 := by
  have hd : m*(m-1) ≤ 2*(m*q)+1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have hm : 2*q+2 ≤ m := by omega
  have hs : 2*q+1 ≤ m-1 := by omega
  have hmul := Nat.mul_le_mul_left m hs
  nlinarith

theorem positiveTargets_card {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (positiveTargets T label F A G q x hr).card ≤ 2*q+1 := by
  let S := positiveTargets T label F A G q x hr
  have hgate : ∀ j ∈ S, ∀ c, F G (recursiveChild x j c) = true := by
    intro j hj c
    obtain ⟨hj, hgate⟩ := Finset.mem_filter.mp hj
    by_cases hc : c = missingWitness F A x hr j
    · simpa only [hc] using hgate
    · exact hF.accepts_of_le hGA
        (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hj).2.1 c hc)
  have hlocal : ∀ i ∈ S, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    have hsub : S.filter (T.Adj i) ⊆ failedGuards T label F G x i := by
      intro j hj
      obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
      exact (mem_failedGuards T label F G x i j).mpr ⟨hij, hgate j hj _⟩
    exact (Finset.card_le_card hsub).trans
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2
  apply source_card_arithmetic
  calc
    S.card.choose 2 = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
      rw [T.sum_outdegree_eq, T.card_internalEdges]
    _ ≤ ∑ _i ∈ S, q := Finset.sum_le_sum hlocal
    _ = S.card*q := by simp

def targetCost (q v a b : ℕ) : ℕ :=
  min (v-1) (2*q+1)*a + ((v-1)-min (v-1) (2*q+1))*b

theorem target_charge (q v a b n0 n1 : ℕ) (hba : b ≤ a)
    (hcard : n0+n1 ≤ v-1) (hpos : n1 ≤ 2*q+1) :
    n1*a+n0*b ≤ targetCost q v a b := by
  let l := min (v-1) (2*q+1)
  have hn1 : n1 ≤ l := le_min (by omega) hpos
  have hn0 : n0 ≤ ((v-1)-l)+(l-n1) := by
    have hl : l ≤ v-1 := min_le_left _ _
    omega
  have hm := Nat.mul_le_mul_right b hn0
  have hb := Nat.mul_le_mul_left (l-n1) hba
  have he : n1*a+(l-n1)*a = l*a := by
    rw [← Nat.add_mul]
    congr 1
    omega
  change n1*a+n0*b ≤ l*a+((v-1)-l)*b
  calc
    n1*a+n0*b ≤ n1*a+(((v-1)-l)+(l-n1))*b := Nat.add_le_add_left hm _
    _ = (n1*a+(l-n1)*b)+((v-1)-l)*b := by ring
    _ ≤ (n1*a+(l-n1)*a)+((v-1)-l)*b :=
      Nat.add_le_add_right (Nat.add_le_add_left hb _) _
    _ = _ := by rw [he]

theorem targetCost_mul (q v a b u : ℕ) :
    targetCost q v (a*u) (b*u) = targetCost q v a b*u := by
  simp only [targetCost, Nat.add_mul, Nat.mul_assoc]

end
end SensitivityQ

/- Bundled unchanged module: GenericTargetSplit -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators
namespace SensitivityQ
noncomputable section

/-- Target repairs in the second class pay both the original target joint bound
and the additional gate/target joint bound. -/
def splitTargetChanges {n k r : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (Ai Aj A0 G : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (TC : Finset (Fin k)) (tw : Fin k → Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  TC.biUnion fun i => if F G (recursiveChild x i (tw i)) = true
    then childJointChanges F Ai Aj x i (tw i)
    else childJointChanges F Ai Aj x i (tw i) ∩ childJointChanges F A0 Aj x i (tw i)

theorem splitTargetChanges_card_count {n k r : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (Ai Aj A0 G : Fin n)
    (hA : Ai ≤ Aj) (h0 : A0 ≤ Aj) (Z : Fin n → Fin n → ℕ) (hZ : PairBound F false Z)
    (x : ((Fin k × Fin r) × I) → Bool) (TC : Finset (Fin k)) (tw : Fin k → Fin r)
    (hweak : ∀ i ∈ TC, F Ai (recursiveChild x i (tw i)) = false)
    (hstrong : ∀ i ∈ TC, F Aj (recursiveChild x i (tw i)) = false)
    (hzero : ∀ i ∈ TC, F G (recursiveChild x i (tw i)) ≠ true →
      F A0 (recursiveChild x i (tw i)) = false) :
    (splitTargetChanges F Ai Aj A0 G x TC tw).card ≤
      (TC.filter fun i => F G (recursiveChild x i (tw i)) = true).card*Z Ai Aj +
      (TC.card-(TC.filter fun i => F G (recursiveChild x i (tw i)) = true).card)*
        min (Z Ai Aj) (Z A0 Aj) := by
  let P := TC.filter fun i => F G (recursiveChild x i (tw i)) = true
  let N := TC.filter fun i => F G (recursiveChild x i (tw i)) ≠ true
  have hsum : N.card+P.card = TC.card := by
    have hh := Finset.card_filter_add_card_filter_not (s := TC)
      (fun i => F G (recursiveChild x i (tw i)) = true)
    change P.card+N.card = TC.card at hh
    omega
  have hh : (splitTargetChanges F Ai Aj A0 G x TC tw).card ≤
      ∑ i ∈ TC, if F G (recursiveChild x i (tw i)) = true then Z Ai Aj
        else min (Z Ai Aj) (Z A0 Aj) := by
    apply le_trans Finset.card_biUnion_le
    apply Finset.sum_le_sum
    intro i hi
    by_cases hp : F G (recursiveChild x i (tw i)) = true
    · rw [if_pos hp, if_pos hp, childJointChanges_card]
      exact hZ _ _ hA _ (hweak i hi) (hstrong i hi)
    · rw [if_neg hp, if_neg hp]
      apply le_min
      · exact (Finset.card_le_card Finset.inter_subset_left).trans (by
          rw [childJointChanges_card]
          exact hZ _ _ hA _ (hweak i hi) (hstrong i hi))
      · exact (Finset.card_le_card Finset.inter_subset_right).trans (by
          rw [childJointChanges_card]
          exact hZ _ _ h0 _ (hzero i hi hp) (hstrong i hi))
  have he : (∑ i ∈ TC, if F G (recursiveChild x i (tw i)) = true then Z Ai Aj
        else min (Z Ai Aj) (Z A0 Aj)) =
      P.card*Z Ai Aj+N.card*min (Z Ai Aj) (Z A0 Aj) := by
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, P, N]
  have heN : N.card = TC.card-P.card := by omega
  simpa only [heN] using hh.trans he.le

theorem splitTargetChanges_card {n k r : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (Ai Aj A0 G : Fin n)
    (hA : Ai ≤ Aj) (h0 : A0 ≤ Aj) (Z : Fin n → Fin n → ℕ) (hZ : PairBound F false Z)
    (x : ((Fin k × Fin r) × I) → Bool) (TC : Finset (Fin k)) (tw : Fin k → Fin r)
    (q v : ℕ) (hTC : TC.card ≤ v-1)
    (hP : (TC.filter fun i => F G (recursiveChild x i (tw i)) = true).card ≤ 2*q+1)
    (hweak : ∀ i ∈ TC, F Ai (recursiveChild x i (tw i)) = false)
    (hstrong : ∀ i ∈ TC, F Aj (recursiveChild x i (tw i)) = false)
    (hzero : ∀ i ∈ TC, F G (recursiveChild x i (tw i)) ≠ true →
      F A0 (recursiveChild x i (tw i)) = false) :
    (splitTargetChanges F Ai Aj A0 G x TC tw).card ≤
      targetCost q v (Z Ai Aj) (min (Z Ai Aj) (Z A0 Aj)) := by
  let P := TC.filter fun i => F G (recursiveChild x i (tw i)) = true
  let N := TC.filter fun i => F G (recursiveChild x i (tw i)) ≠ true
  have hsum : N.card+P.card = TC.card := by
    have hh := Finset.card_filter_add_card_filter_not (s := TC)
      (fun i => F G (recursiveChild x i (tw i)) = true)
    change P.card+N.card = TC.card at hh
    omega
  have hh : (splitTargetChanges F Ai Aj A0 G x TC tw).card ≤
      ∑ i ∈ TC, if F G (recursiveChild x i (tw i)) = true then Z Ai Aj
        else min (Z Ai Aj) (Z A0 Aj) := by
    apply le_trans Finset.card_biUnion_le
    apply Finset.sum_le_sum
    intro i hi
    by_cases hp : F G (recursiveChild x i (tw i)) = true
    · rw [if_pos hp, if_pos hp, childJointChanges_card]
      exact hZ _ _ hA _ (hweak i hi) (hstrong i hi)
    · rw [if_neg hp, if_neg hp]
      apply le_min
      · exact (Finset.card_le_card Finset.inter_subset_left).trans (by
          rw [childJointChanges_card]
          exact hZ _ _ hA _ (hweak i hi) (hstrong i hi))
      · exact (Finset.card_le_card Finset.inter_subset_right).trans (by
          rw [childJointChanges_card]
          exact hZ _ _ h0 _ (hzero i hi hp) (hstrong i hi))
  have he : (∑ i ∈ TC, if F G (recursiveChild x i (tw i)) = true then Z Ai Aj
        else min (Z Ai Aj) (Z A0 Aj)) =
      P.card*Z Ai Aj+N.card*min (Z Ai Aj) (Z A0 Aj) := by
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, P, N]
  exact hh.trans (he.le.trans (target_charge q v _ _ _ _ (min_le_left _ _)
    (by omega) hP))




theorem strict_split_pair_zero {n k r v : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (qi qj : ℕ) (hq : qj < qi) (hDefect : DefectBound T label qj v)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (Z : Fin n → Fin n → ℕ) (hZ : PairBound F false Z)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hGA : Gi ≤ Ai)
    (hZle : Z Gj Aj ≤ Z Ai Aj)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T label F Ai Gi qi x = false)
    (hx' : tolerantFamily T label F Aj Gj qj x = false) :
    jointSensitivityAt (tolerantFamily T label F Ai Gi qi)
      (tolerantFamily T label F Aj Gj qj) x ≤ targetCost qj v (Z Ai Aj) (Z Gj Aj) := by
  let TC := tolerantTargets T label F Aj Gj qj x
  let tw := missingWitness F Aj x hr
  let U := splitTargetChanges F Ai Aj Gj Gj x TC tw
  have hGJA : Gj ≤ Aj := hG.trans (hGA.trans hA)
  have hsub : jointChanges (tolerantFamily T label F Ai Gi qi)
      (tolerantFamily T label F Aj Gj qj) x ⊆ U := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T label F Aj Gj qj (flip x {((j,c),a)}) = true := by
      simpa only [hx', Bool.not_eq_false] using hc.2
    obtain ⟨i, hi⟩ := (tolerantFamily_true T label F Aj Gj qj _).mp hon
    have hoff := (tolerantFamily_false T label F Aj Gj qj x).mp hx' i
    rcases tolerant_repair_cases T label F Aj Gj qj x i j c a hoff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, _⟩
    · subst j
      have hcw := missingWitness_unique F Aj x hr i (Finset.mem_filter.mp hit).2.1 c htoff
      have hwo : F Ai (recursiveChild x i c) = false := by
        rw [hcw]
        exact tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
          (Nat.le_of_lt hq) hr hx hit
      have hwn := hF.accepts_of_le hA hton
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
          F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
        simp [hwo, hwn, htoff, hton]
      by_cases hgo : F Gj (recursiveChild x i (tw i)) = true
      · rw [if_pos hgo]
        simpa [childJointChanges, tw, hcw] using hn
      · rw [if_neg hgo]
        apply Finset.mem_inter.mpr
        constructor
        · simpa [childJointChanges, tw, hcw] using hn
        · have hgoff : F Gj (recursiveChild x i c) = false := by
            simpa only [tw, ← hcw, Bool.not_eq_true] using hgo
          have hgn := hF.accepts_of_le hGJA hton
          have hn0 : F Gj (flip (recursiveChild x i c) {a}) ≠ F Gj (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
            simp [hgoff, hgn, htoff, hton]
          simpa [childJointChanges, tw, hcw] using hn0
    · exact False.elim (no_guard_candidate_of_strict T label F hF
        Ai Aj Gi Gj hA hG x hq hx hig)
  have hc : U.card ≤ targetCost qj v (Z Ai Aj) (Z Gj Aj) := by
    have hh := splitTargetChanges_card F Ai Aj Gj Gj hA hGJA Z hZ x TC tw qj v
      (targets_card T label hDefect F hF Aj Gj hGJA x hr)
      (positiveTargets_card T label F hF Aj Gj hGJA qj x hr)
      (fun i hi => tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
        (Nat.le_of_lt hq) hr hx hi)
      (fun i hi => missingWitness_false F Aj x hr i (Finset.mem_filter.mp hi).2.1)
      (fun i hi hn => Bool.eq_false_iff.mpr hn)
    simpa only [min_eq_right hZle] using hh
  exact (Finset.card_le_card hsub).trans hc

theorem aux_split_positive_zero {n k q v : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hDefect : DefectBound T label q v) (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A B G : Fin n) (hAB : A ≤ B) (hGB : G ≤ B)
    (Z : Fin n → Fin n → ℕ) (hZ : PairBound F false Z)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : auxFamily s F A x = false)
    (hx' : tolerantFamily T label F B G q x = false) :
    jointSensitivityAt (auxFamily s F A) (tolerantFamily T label F B G q) x ≤
      targetCost q v (Z A B) (min (Z A B) (Z (min A G) B)) := by
  let TC := tolerantTargets T label F B G q x
  let tw := missingWitness F B x (by decide)
  let U := splitTargetChanges F A B (min A G) G x TC tw
  have h0B : min A G ≤ B := (min_le_left _ _).trans hAB
  have hweak : ∀ i ∈ TC, F A (recursiveChild x i (tw i)) = false := by
    intro i hi
    exact aux_target_false s F hF A B hAB x hx i (Finset.mem_filter.mp hi).2.1
  have hzero : ∀ i ∈ TC, F G (recursiveChild x i (tw i)) ≠ true →
      F (min A G) (recursiveChild x i (tw i)) = false := by
    intro i hi hn
    by_cases hAG : A ≤ G
    · simpa only [min_eq_left hAG] using hweak i hi
    · simpa only [min_eq_right (le_of_not_ge hAG)] using Bool.eq_false_iff.mpr hn
  have hsub : jointChanges (auxFamily s F A) (tolerantFamily T label F B G q) x ⊆ U := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T label F B G q (flip x {((j,c),a)}) = true := by
      simpa only [hx', Bool.not_eq_false] using hc.2
    obtain ⟨hit, he, hao, hbo, hbn⟩ := aux_target_repair T label s F hF A B G hAB q x hx hx' j c a hon
    have han := hF.accepts_of_le hAB hbn
    apply Finset.mem_biUnion.mpr
    refine ⟨j, hit, ?_⟩
    have hn : F A (flip (recursiveChild x j c) {a}) ≠ F A (recursiveChild x j c) ∧
        F B (flip (recursiveChild x j c) {a}) ≠ F B (recursiveChild x j c) := by
      simp [hao,han,hbo,hbn]
    by_cases hgo : F G (recursiveChild x j (tw j)) = true
    · rw [if_pos hgo]
      simpa [childJointChanges,tw,he] using hn
    · rw [if_neg hgo]
      apply Finset.mem_inter.mpr
      constructor
      · simpa [childJointChanges,tw,he] using hn
      · have h0off : F (min A G) (recursiveChild x j c) = false := by
          simpa only [tw, ← he] using hzero j hit hgo
        have h0on := hF.accepts_of_le h0B hbn
        have hn0 : F (min A G) (flip (recursiveChild x j c) {a}) ≠
              F (min A G) (recursiveChild x j c) ∧
            F B (flip (recursiveChild x j c) {a}) ≠ F B (recursiveChild x j c) := by
          simp [h0off,h0on,hbo,hbn]
        simpa [childJointChanges,tw,he] using hn0
  have hh := splitTargetChanges_card F A B (min A G) G hAB h0B Z hZ x TC tw q v
    (targets_card T label hDefect F hF B G hGB x (by decide))
    (positiveTargets_card T label F hF B G hGB q x (by decide))
    hweak
    (fun i hi => missingWitness_false F B x (by decide) i (Finset.mem_filter.mp hi).2.1)
    hzero
  exact (Finset.card_le_card hsub).trans hh

end
end SensitivityQ

/- Bundled unchanged module: TargetGuardCoupling -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators

namespace SensitivityQ
noncomputable section

/-- Positive target sources and guard sources both have completely accepting
gate rows. Counting internal arcs in their disjoint union couples their sizes.
No defect-labeling hypothesis or side-sensitivity profile is needed here. -/
theorem positiveTargets_guards_coupling {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    ((positiveTargets T label F A G q x hr).card +
      (tolerantGuards T label F A G q x).card).choose 2 ≤
      q * (positiveTargets T label F A G q x hr).card +
      (q+1) * (tolerantGuards T label F A G q x).card := by
  let P := positiveTargets T label F A G q x hr
  let GC := tolerantGuards T label F A G q x
  let S := P ∪ GC
  have hdis : Disjoint P GC := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiGC
    have hone : (missingTargets F A x i).card = 1 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hiP).1).2.1
    have hempty : missingTargets F A x i = ∅ :=
      (Finset.mem_filter.mp hiGC).2.1
    simp only [hempty, Finset.card_empty] at hone
    omega
  have hgate : ∀ j ∈ S, ∀ c, F G (recursiveChild x j c) = true := by
    intro j hj c
    rcases Finset.mem_union.mp hj with hjP | hjGC
    · obtain ⟨hjTC, hpass⟩ := Finset.mem_filter.mp hjP
      by_cases hc : c = missingWitness F A x hr j
      · simpa only [hc] using hpass
      · exact hF.accepts_of_le hGA
          (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hjTC).2.1 c hc)
    · exact hF.accepts_of_le hGA
        ((missingTargets_empty F A x j).mp (Finset.mem_filter.mp hjGC).2.1 c)
  have hsub (i : Fin k) : S.filter (T.Adj i) ⊆ failedGuards T label F G x i := by
    intro j hj
    obtain ⟨hjS, hij⟩ := Finset.mem_filter.mp hj
    exact (mem_failedGuards T label F G x i j).mpr ⟨hij, hgate j hjS _⟩
  have hlocalP : ∀ i ∈ P, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    exact (Finset.card_le_card (hsub i)).trans
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2
  have hlocalGC : ∀ i ∈ GC, (S.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have he : (failedGuards T label F G x i).card = q+1 :=
      (Finset.mem_filter.mp hi).2.2
    exact (Finset.card_le_card (hsub i)).trans (Nat.le_of_eq he)
  change (P.card + GC.card).choose 2 ≤ q*P.card + (q+1)*GC.card
  calc
    (P.card + GC.card).choose 2 = S.card.choose 2 := by
      rw [show S.card = P.card + GC.card from Finset.card_union_of_disjoint hdis]
    _ = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
      rw [T.sum_outdegree_eq, T.card_internalEdges]
    _ = (∑ i ∈ P, (S.filter (T.Adj i)).card) +
        ∑ i ∈ GC, (S.filter (T.Adj i)).card := Finset.sum_union hdis
    _ ≤ (∑ _i ∈ P, q) + ∑ _i ∈ GC, (q+1) :=
      Nat.add_le_add (Finset.sum_le_sum hlocalP) (Finset.sum_le_sum hlocalGC)
    _ = q*P.card + (q+1)*GC.card := by simp [Nat.mul_comm]

end
end SensitivityQ

/- Bundled unchanged module: GenericCoupledZero -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators
namespace SensitivityQ
noncomputable section

/-- Simultaneous target and guard charge. The tournament degree inequality
restricts the two source counts before taking the maximum. -/
def coupledCost (q v a b c e : ℕ) : ℕ :=
  (Finset.range (2*q+2)).sup fun n =>
    (Finset.range (2*q+4)).sup fun m =>
      if (n+m).choose 2 ≤ q*n+(q+1)*m then
        n*a+((v-1)-n)*b+((m*(q+1)-m.choose 2)*c+m.choose 2*e)
      else 0

theorem charge_le_coupledCost (q v a b c e n m : ℕ)
    (hn : n ≤ 2*q+1) (hm : m ≤ 2*q+3)
    (hc : (n+m).choose 2 ≤ q*n+(q+1)*m) :
    n*a+((v-1)-n)*b+((m*(q+1)-m.choose 2)*c+m.choose 2*e) ≤
      coupledCost q v a b c e := by
  have hi : n*a+((v-1)-n)*b+((m*(q+1)-m.choose 2)*c+m.choose 2*e) ≤
      (Finset.range (2*q+4)).sup fun m =>
        if (n+m).choose 2 ≤ q*n+(q+1)*m then
          n*a+((v-1)-n)*b+((m*(q+1)-m.choose 2)*c+m.choose 2*e)
        else 0 := by
    have hh := Finset.le_sup (s := Finset.range (2*q+4)) (b := m)
      (f := fun m => if (n+m).choose 2 ≤ q*n+(q+1)*m then
        n*a+((v-1)-n)*b+((m*(q+1)-m.choose 2)*c+m.choose 2*e) else 0)
      (Finset.mem_range.mpr (by omega))
    simpa only [if_pos hc] using hh
  exact hi.trans (Finset.le_sup (s := Finset.range (2*q+2)) (b := n)
    (f := fun n => (Finset.range (2*q+4)).sup fun m =>
      if (n+m).choose 2 ≤ q*n+(q+1)*m then
        n*a+((v-1)-n)*b+((m*(q+1)-m.choose 2)*c+m.choose 2*e) else 0)
    (Finset.mem_range.mpr (by omega)))

theorem coupledCost_mul (q v a b c e u : ℕ) :
    coupledCost q v (a*u) (b*u) (c*u) (e*u) = coupledCost q v a b c e*u := by
  unfold coupledCost
  rw [Finset.sup_mul₀]
  congr 1
  funext n
  rw [Finset.sup_mul₀]
  congr 1
  funext m
  split_ifs <;> simp only [Nat.zero_mul, Nat.add_mul, Nat.mul_assoc]

theorem coupled_pair_zero {n k r q v : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r) (hDefect : DefectBound T label q v)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (Z Y : Fin n → Fin n → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hGA : Gi ≤ Ai)
    (hZle : Z Gj Aj ≤ Z Ai Aj)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T label F Ai Gi q x = false)
    (hx' : tolerantFamily T label F Aj Gj q x = false) :
    jointSensitivityAt (tolerantFamily T label F Ai Gi q)
      (tolerantFamily T label F Aj Gj q) x ≤
      coupledCost q v (Z Ai Aj) (Z Gj Aj) (Y Gj Gi) (Y Gj Aj) := by
  let TC := tolerantTargets T label F Aj Gj q x
  let GC := tolerantGuards T label F Aj Gj q x
  let P := positiveTargets T label F Aj Gj q x hr
  let tw := missingWitness F Aj x hr
  let B := failedGuards T label F Gj x
  let U := splitTargetChanges F Ai Aj Gj Gj x TC tw
  let V := GC.biUnion fun i => (B i).biUnion fun j =>
    if j ∈ GC then childJointChanges F Gj Aj x j (label i j)
      else childJointChanges F Gj Gi x j (label i j)
  have hGJA : Gj ≤ Aj := hG.trans (hGA.trans hA)
  have hweakguard : ∀ i ∈ GC, ∀ j ∈ B i,
      F Gi (recursiveChild x j (label i j)) = true := by
    intro i hi j hj
    have he := tolerant_guard_sets_eq T label F hF Ai Aj Gi Gj hA hG x q hx hi
    have hj' : j ∈ failedGuards T label F Gi x i := by rw [he]; exact hj
    exact ((mem_failedGuards T label F Gi x i j).mp hj').2
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T label F Ai Gi q (flip x {p}) ≠ tolerantFamily T label F Ai Gi q x ∧
      tolerantFamily T label F Aj Gj q (flip x {p}) ≠ tolerantFamily T label F Aj Gj q x) ⊆
      U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)}) = true := by
      cases hy : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)})
      · exact False.elim (hc.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi⟩ := (tolerantFamily_true T label F Aj Gj q _).mp hon
    have hoff := (tolerantFamily_false T label F Aj Gj q x).mp hx' i
    rcases tolerant_repair_cases T label F Aj Gj q x i j c a hoff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, hcl, hgon, hgoff⟩
    · subst j
      have hcw := missingWitness_unique F Aj x hr i (Finset.mem_filter.mp hit).2.1 c htoff
      have hwo : F Ai (recursiveChild x i c) = false := by
        rw [hcw]
        exact tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
          (le_refl q) hr hx hit
      have hwn := hF.accepts_of_le hA hton
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
          F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
        simp [hwo, hwn, htoff, hton]
      by_cases hgo : F Gj (recursiveChild x i (tw i)) = true
      · rw [if_pos hgo]
        simpa [childJointChanges, tw, hcw] using hn
      · rw [if_neg hgo]
        apply Finset.mem_inter.mpr
        constructor
        · simpa [childJointChanges, tw, hcw] using hn
        · have hgoff : F Gj (recursiveChild x i c) = false := by
            simpa only [tw, ← hcw, Bool.not_eq_true] using hgo
          have hgn := hF.accepts_of_le hGJA hton
          have hn0 : F Gj (flip (recursiveChild x i c) {a}) ≠ F Gj (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
            simp [hgoff, hgn, htoff, hton]
          simpa [childJointChanges, tw, hcw] using hn0
    · subst c
      have hj : j ∈ B i := (mem_failedGuards T label F Gj x i j).mpr ⟨hij, hgon⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hig, Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩⟩
      by_cases hjG : j ∈ GC
      · rw [if_pos hjG]
        have hto := (missingTargets_empty F Aj x j).mp (Finset.mem_filter.mp hjG).2.1 (label i j)
        have htf := hF.rejects_of_le hGJA hgoff
        have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gj (recursiveChild x j (label i j)) ∧
            F Aj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Aj (recursiveChild x j (label i j)) := by simp [hgon, hgoff, hto, htf]
        simpa [childJointChanges] using hn
      · rw [if_neg hjG]
        have hwo := hweakguard i hig j hj
        have hwf := hF.rejects_of_le hG hgoff
        have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gj (recursiveChild x j (label i j)) ∧
            F Gi (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gi (recursiveChild x j (label i j)) := by simp [hgon, hgoff, hwo, hwf]
        simpa [childJointChanges] using hn
  have hU : U.card ≤ P.card*Z Ai Aj+((v-1)-P.card)*Z Gj Aj := by
    have hh := splitTargetChanges_card_count F Ai Aj Gj Gj hA hGJA Z hZ x TC tw
      (fun i hi => tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
        (le_refl q) hr hx hi)
      (fun i hi => missingWitness_false F Aj x hr i (Finset.mem_filter.mp hi).2.1)
      (fun i hi hn => Bool.eq_false_iff.mpr hn)
    have hU0 : U.card ≤ P.card*Z Ai Aj+(TC.card-P.card)*Z Gj Aj := by
      simpa only [U, P, positiveTargets, TC, tw, min_eq_right hZle] using hh
    have hTC := targets_card T label hDefect F hF Aj Gj hGJA x hr
    exact hU0.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hTC P.card)) _)
  have hV : V.card ≤ (GC.card*(q+1)-GC.card.choose 2)*Y Gj Gi+
      GC.card.choose 2*Y Gj Aj := by
    apply le_trans Finset.card_biUnion_le
    apply le_trans (Finset.sum_le_sum (fun i hi => Finset.card_biUnion_le))
    apply le_trans (Finset.sum_le_sum ?_) (guard_charge T label F hF Aj Gj hGJA q x
      (Y Gj Gi) (Y Gj Aj)).le
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hgo := ((mem_failedGuards T label F Gj x i j).mp hj).2
    by_cases hjG : j ∈ GC
    · rw [if_pos hjG, if_pos hjG, childJointChanges_card]
      exact hY _ _ hGJA _ hgo
        ((missingTargets_empty F Aj x j).mp (Finset.mem_filter.mp hjG).2.1 _)
    · rw [if_neg hjG, if_neg hjG, childJointChanges_card]
      exact hY _ _ hG _ hgo (hweakguard i hi j hj)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  change jointSensitivityAt _ _ x ≤ _ at hh
  have hnum := charge_le_coupledCost q v (Z Ai Aj) (Z Gj Aj) (Y Gj Gi) (Y Gj Aj)
    P.card GC.card (positiveTargets_card T label F hF Aj Gj hGJA q x hr)
    (guards_card T label F hF Aj Gj hGJA q x)
    (positiveTargets_guards_coupling T label F hF Aj Gj hGJA q x hr)
  exact hh.trans ((Nat.add_le_add hU hV).trans hnum)

end
end SensitivityQ

/- Bundled unchanged module: Definitions.LocalRefinedCore -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open OAI.Paper320 Sensitivity205
open scoped Classical

namespace Sensitivity2075
noncomputable section

section Geometry
variable {k r h : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin (h+1) → (I → Bool) → Bool)
  (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)

include hF in
/-- An ordinary gate extends all target candidates to a coherent set.

The missing gate child has the strongest target predicate false. Thus when its
row is a target candidate its label is already the unique missing target label.
The old coupled estimate used this extension only when two gates were present.
-/
theorem targets_card_with_one_ordinary {t : ℕ} (A : Labeling T r t)
    (heq : A.label = label) (hr : 0 < r)
    {b : Fin k} (hb : b ∈ gateCandidates T label F q x)
    (hbo : F (Fin.last h) (recursiveChild x (gateWitness T label F q x b)
      (label b (gateWitness T label F q x b))) = false) :
    (targetCandidates T label F q x).card ≤ t-2 := by
  have hbnot : b ∉ targetCandidates T label F q x := by
    intro hbt
    exact Finset.disjoint_left.mp
      (Sensitivity20635.target_gate_disjoint T label F q x) hbt hb
  have hc : ((targetCandidates T label F q x) ∪ {b}).card < t := by
    apply A.coherent_card _ (targetWitness F x hr)
    intro i hi j hj hij
    rw [heq]
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hi with hi | hi
      · apply Sensitivity20635.target_incoming_label T label F hF q x hr hj
        exact (gateFailures_empty_iff T label F q x i).mp
          (Finset.mem_filter.mp hi).2.2 j hij
      · have hib : i = b := Finset.mem_singleton.mp hi
        subst i
        by_cases hej : j = gateWitness T label F q x b
        · subst j
          exact targetWitness_unique T label F q x hr _ hj _ hbo
        · apply Sensitivity20635.target_incoming_label T label F hF q x hr hj
          exact Sensitivity20635.gate_passes T label F q x hb hij hej
    · have hjb : j = b := Finset.mem_singleton.mp hj
      subst j
      rcases Finset.mem_union.mp hi with hi | hi
      · exact False.elim
          (Sensitivity20635.target_not_to_gate T label F hF q x hi hb hij)
      · have hib : i = b := Finset.mem_singleton.mp hi
        subst i
        exact False.elim (T.ne_of_adj hij rfl)
  rw [Finset.card_union_of_disjoint] at hc
  · simp only [Finset.card_singleton] at hc
    omega
  · exact Finset.disjoint_singleton_right.mpr hbnot

end Geometry

/-- Exact numerical consequence of the new one-ordinary-gate coherence bound. -/
theorem coupled_weighted_bound_refined (n0 n1 m0 m1 t A B J K : ℕ)
    (ht : 4 ≤ t) (hJA : J ≤ A) (hKB : K ≤ B)
    (hn1 : n1 ≤ 1) (hm0 : m0 ≤ 1) (hm : m0 + m1 ≤ 3)
    (hn : n0 + n1 ≤ t - 1)
    (hordinary : 0 < m0 → n0 + n1 ≤ t - 2)
    (hnzero : 2 ≤ m0 + m1 → n1 = 0)
    (htwo0 : m0 + m1 = 2 → m0 = 0 → n0 ≤ t - 2)
    (htwo1 : m0 + m1 = 2 → m0 = 1 → n0 ≤ t - 3)
    (hthree : m0 + m1 = 3 → m0 = 0 ∧ n0 ≤ t - 4) :
    n1 * A + n0 * J + m0 * B + m1 * K ≤
      max (max (max (max (A+B+(t-3)*J) (A+K+(t-2)*J))
        (B+K+(t-3)*J)) (2*K+(t-2)*J)) (3*K+(t-4)*J) := by
  let R := max (max (max (max (A+B+(t-3)*J) (A+K+(t-2)*J))
      (B+K+(t-3)*J)) (2*K+(t-2)*J)) (3*K+(t-4)*J)
  have hR0 : A+B+(t-3)*J ≤ R :=
    (le_max_left _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans (le_max_left _ _)))
  have hR1 : A+K+(t-2)*J ≤ R :=
    (le_max_right _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans (le_max_left _ _)))
  have hR2 : B+K+(t-3)*J ≤ R :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hR3 : 2*K+(t-2)*J ≤ R :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hR4 : 3*K+(t-4)*J ≤ R := le_max_right _ _
  change _ ≤ R
  by_cases hsmall : m0 + m1 ≤ 1
  · by_cases hmzero : m0 = 0
    · have hm1 : m1 ≤ 1 := by omega
      have hgate : m0*B+m1*K ≤ K := by
        simp only [hmzero, Nat.zero_mul, Nat.zero_add]
        simpa using Nat.mul_le_mul_right K hm1
      have htargets : n1*A+n0*J ≤ A+(t-2)*J := by
        have ht2 : t-2+1 = t-1 := _root_.SensitivityProofArithmetic.sub_two_add_one_explicit t (Nat.le_trans (by decide : 2 ≤ 4) ht)
        interval_cases n1
        · have hmul := Nat.mul_le_mul_right J hn
          simp only [Nat.add_zero, Nat.zero_mul] at *
          rw [← ht2, Nat.add_mul, Nat.one_mul] at hmul
          omega
        · have hbound : n0 ≤ t-2 := by omega
          have hmul := Nat.mul_le_mul_right J hbound
          simp only [Nat.one_mul]
          omega
      exact (show n1*A+n0*J+m0*B+m1*K ≤ A+K+(t-2)*J by omega).trans hR1
    · have hmzero : m0 = 1 := by omega
      have hmone : m1 = 0 := by omega
      have hn' : n0 + n1 ≤ t-2 := hordinary (by omega)
      have htargets : n1*A+n0*J ≤ A+(t-3)*J := by
        have ht3 : t-3+1 = t-2 := by omega
        interval_cases n1
        · have hmul := Nat.mul_le_mul_right J hn'
          simp only [Nat.add_zero, Nat.zero_mul] at *
          rw [← ht3, Nat.add_mul, Nat.one_mul] at hmul
          omega
        · have hbound : n0 ≤ t-3 := by omega
          have hmul := Nat.mul_le_mul_right J hbound
          simp only [Nat.one_mul]
          omega
      exact (show n1*A+n0*J+m0*B+m1*K ≤ A+B+(t-3)*J by
        simp only [hmzero, hmone, Nat.one_mul, Nat.zero_mul]; omega).trans hR0
  · have hnzero' := hnzero (by omega)
    subst n1
    by_cases htwo : m0+m1=2
    · interval_cases m0
      · have hbound := htwo0 htwo rfl
        have hm1 : m1 = 2 := by omega
        subst m1
        have hmul := Nat.mul_le_mul_right J hbound
        exact (show 0*A+n0*J+0*B+2*K ≤ 2*K+(t-2)*J by omega).trans hR3
      · have hbound := htwo1 htwo rfl
        have hm1 : m1 = 1 := by omega
        subst m1
        have hmul := Nat.mul_le_mul_right J hbound
        exact (show 0*A+n0*J+1*B+1*K ≤ B+K+(t-3)*J by omega).trans hR2
    · have hsum : m0+m1=3 := by omega
      obtain ⟨hmzero, hbound⟩ := hthree hsum
      subst m0
      have hm1 : m1=3 := by omega
      subst m1
      have hmul := Nat.mul_le_mul_right J hbound
      exact (show 0*A+n0*J+0*B+3*K ≤ 3*K+(t-4)*J by omega).trans hR4




end
end Sensitivity2075


/-! Generic refined zero-side transfer. The function construction, all
one-side estimates, and block witnesses are the accepted construction. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
open Sensitivity20635 Sensitivity2075
open scoped BigOperators
namespace SensitivityRefined
noncomputable section

theorem mixed_pair_zero_coupled {n k r t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : Labeling T r t)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (ht : 4 ≤ t)
    (Z Y : Fin n → Fin n → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hGA : Gi ≤ Ai)
    (hZA : Z Gj Aj ≤ Z Ai Aj) (hYK : Y Gj Aj ≤ Y Gj Gi)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : mixedFamily T A.label F Ai Gi x = false)
    (hx' : mixedFamily T A.label F Aj Gj x = false) :
    jointSensitivityAt (mixedFamily T A.label F Ai Gi)
      (mixedFamily T A.label F Aj Gj) x ≤
      max (max (max (max (Z Ai Aj + Y Gj Gi + (t-3)*Z Gj Aj)
        (Z Ai Aj + Y Gj Aj + (t-2)*Z Gj Aj))
        (Y Gj Gi + Y Gj Aj + (t-3)*Z Gj Aj))
        (2*Y Gj Aj + (t-2)*Z Gj Aj))
        (3*Y Gj Aj + (t-4)*Z Gj Aj) := by
  let S := twoPred F Gj Aj
  have hS : NestedFamily S := twoPred_nested F hF Gj Aj (hG.trans (hGA.trans hA))
  let TC := targetCandidates T A.label S 0 x
  let GC := gateCandidates T A.label S 0 x
  let tw := targetWitness S x hr
  let gw := gateWitness T A.label S 0 x
  let T0 := TC.filter fun i => F Gj (recursiveChild x i (tw i)) = false
  let T1 := TC.filter fun i => F Gj (recursiveChild x i (tw i)) = true
  let G0 := GC.filter fun i => F Aj (recursiveChild x (gw i) (A.label i (gw i))) = false
  let G1 := GC.filter fun i => F Aj (recursiveChild x (gw i) (A.label i (gw i))) = true
  let U := T1.biUnion fun i => childJointChanges F Ai Aj x i (tw i)
  let V := T0.biUnion fun i => childJointChanges F Gj Aj x i (tw i)
  let W := G0.biUnion fun i => childJointChanges F Gj Gi x (gw i) (A.label i (gw i))
  let X := G1.biUnion fun i => childJointChanges F Gj Aj x (gw i) (A.label i (gw i))
  have hsub : (Finset.univ.filter fun p =>
      mixedFamily T A.label F Ai Gi (flip x {p}) ≠ mixedFamily T A.label F Ai Gi x ∧
      mixedFamily T A.label F Aj Gj (flip x {p}) ≠ mixedFamily T A.label F Aj Gj x) ⊆
      (U ∪ V) ∪ (W ∪ X) := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon' : mixedFamily T A.label F Aj Gj (flip x {((j,c),a)}) = true := by
      cases hy : mixedFamily T A.label F Aj Gj (flip x {((j,c),a)})
      · exact False.elim (hc.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T A.label S 0 _).mp hon'
    have hioff := (recursiveFamily_eq_false_iff T A.label S 0 x).mp hx' i
    rcases rowClause_repair_cases T A.label S 0 x i j c a hioff hi' with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      change F Aj (recursiveChild x i c) = false at htoff
      change F Aj (flip (recursiveChild x i c) {a}) = true at hton
      have hcw := targetWitness_unique T A.label S 0 x hr i hit c htoff
      have hweakoff : F Ai (recursiveChild x i c) = false := by
        rw [hcw]
        exact target_candidate_weak_false T A.label F hF Ai Aj Gi Gj hA hG x hr hx hit
      have hweakon := hF.accepts_of_le hA hton
      have hgon := hF.accepts_of_le (hG.trans (hGA.trans hA)) hton
      apply Finset.mem_union_left
      cases hz : F Gj (recursiveChild x i c)
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hz
        · have hn : F Gj (flip (recursiveChild x i c) {a}) ≠
                F Gj (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠
                F Aj (recursiveChild x i c) := by simp [hgon, hz, hton, htoff]
          simpa [childJointChanges, tw, hcw] using hn
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hz
        · have hn : F Ai (flip (recursiveChild x i c) {a}) ≠
                F Ai (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠
                F Aj (recursiveChild x i c) := by
            simp [hweakon, hweakoff, hton, htoff]
          simpa [childJointChanges, tw, hcw] using hn
    · change F Gj (recursiveChild x j (A.label i j)) = true at hgon
      change F Gj (flip (recursiveChild x j (A.label i j)) {a}) = false at hgoff
      have hjw := gateWitness_unique T A.label S 0 x i hig j hij hgon
      have hwgon := gate_candidate_weak_true T A.label F hF Ai Aj Gi Gj hA hG x hx hig
      have hweakon : F Gi (recursiveChild x j (A.label i j)) = true := by
        simpa [hjw] using hwgon
      have hweakoff := hF.rejects_of_le hG hgoff
      apply Finset.mem_union_right
      cases hto : F Aj (recursiveChild x j (A.label i j))
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hig, ?_⟩, ?_⟩
        · simpa only [gw, ← hjw] using hto
        · have hn : F Gj (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F Gj (recursiveChild x j (A.label i j)) ∧
              F Gi (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F Gi (recursiveChild x j (A.label i j)) := by
            simp [hgon, hgoff, hweakon, hweakoff]
          simpa [childJointChanges, gw, hjw] using hn
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hig, ?_⟩, ?_⟩
        · simpa only [gw, ← hjw] using hto
        · have htf := hF.rejects_of_le (hG.trans (hGA.trans hA)) hgoff
          have hn : F Gj (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F Gj (recursiveChild x j (A.label i j)) ∧
              F Aj (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F Aj (recursiveChild x j (A.label i j)) := by
            simp [hgon, hgoff, hto, htf]
          simpa [childJointChanges, gw, hjw] using hn
  have hU : U.card ≤ T1.card * Z Ai Aj := by
    apply card_biUnion_le_mul
    intro i hi
    rw [childJointChanges_card]
    exact hZ _ _ hA _
      (target_candidate_weak_false T A.label F hF Ai Aj Gi Gj hA hG x hr hx
        (Finset.mem_filter.mp hi).1)
      (targetWitness_false T A.label S 0 x hr i (Finset.mem_filter.mp hi).1)
  have hV : V.card ≤ T0.card * Z Gj Aj := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hi, hz⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hZ _ _ (hG.trans (hGA.trans hA)) _ hz (targetWitness_false T A.label S 0 x hr i hi)
  have hW : W.card ≤ G0.card * Y Gj Gi := by
    apply card_biUnion_le_mul
    intro i hi
    have hg := (Finset.mem_filter.mp hi).1
    rw [childJointChanges_card]
    exact hY _ _ hG _ (gateWitness_spec T A.label S 0 x i hg).2
      (gate_candidate_weak_true T A.label F hF Ai Aj Gi Gj hA hG x hx hg)
  have hX : X.card ≤ G1.card * Y Gj Aj := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hi, ht⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hY _ _ (hG.trans (hGA.trans hA)) _ (gateWitness_spec T A.label S 0 x i hi).2 ht
  have hcost : jointSensitivityAt (mixedFamily T A.label F Ai Gi) (mixedFamily T A.label F Aj Gj) x ≤
      T1.card * Z Ai Aj + T0.card * Z Gj Aj +
      G0.card * Y Gj Gi + G1.card * Y Gj Aj := by
    have hu := Finset.card_union_le U V
    have hw := Finset.card_union_le W X
    have hc := Finset.card_union_le (U ∪ V) (W ∪ X)
    have hs := Finset.card_le_card hsub
    change jointSensitivityAt _ _ x ≤ _ at hs
    omega
  have hnsum : T0.card + T1.card = TC.card := by
    simpa [T0, T1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := TC)
        (fun i => F Gj (recursiveChild x i (tw i)) = false))
  have hmsum : G0.card + G1.card = GC.card := by
    simpa [G0, G1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := GC)
        (fun i => F Aj (recursiveChild x (gw i) (A.label i (gw i))) = false))
  have hn1 : T1.card ≤ 1 := target_sources_card T A.label S hS 0 x hr
  have hm0 : G0.card ≤ 1 := gate_false_targets_card T A.label S hS 0 x
  have hm : G0.card + G1.card ≤ 3 := by
    rw [hmsum]
    exact gateCandidates_card T A.label S hS 0 x
  have hn : T0.card + T1.card ≤ t-1 := by
    have hc := Sensitivity205.targetCandidates_card T A S hS 0 x hr
    change TC.card < t at hc
    omega
  have hordinary : 0 < G0.card → T0.card + T1.card ≤ t-2 := by
    intro hpos
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
    obtain ⟨hb, hbo⟩ := Finset.mem_filter.mp hb
    have hc := targets_card_with_one_ordinary T A.label S hS 0 x A rfl hr hb hbo
    change TC.card ≤ t-2 at hc
    omega
  have hnzero : 2 ≤ G0.card + G1.card → T1.card = 0 := by
    intro hg
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hi, hon⟩ := Finset.mem_filter.mp hi
    have hz := gate_card_two_targets_zero T A.label S hS 0 x hr
      (by simpa [hmsum] using hg) hi
    change F Gj (recursiveChild x i (tw i)) = false at hz
    change F Gj (recursiveChild x i (tw i)) = true at hon
    simp only [hz, Bool.false_eq_true] at hon
  have htwo0 : G0.card + G1.card = 2 → G0.card = 0 → T0.card ≤ t-2 := by
    intro hg _
    have hc := targets_card_sub_two T A.label S hS 0 x A rfl hr (by omega : 2 ≤ GC.card)
    change TC.card ≤ t-2 at hc
    omega
  have htwo1 : G0.card + G1.card = 2 → G0.card = 1 → T0.card ≤ t-3 := by
    intro hg hzero
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < G0.card)
    obtain ⟨hb, hbo⟩ := Finset.mem_filter.mp hb
    have hc := targets_card_with_ordinary T A.label S hS 0 x A rfl hr
      (by omega : 2 ≤ GC.card) hb hbo
    change TC.card + GC.card < t at hc
    omega
  have hthree : G0.card + G1.card = 3 → G0.card = 0 ∧ T0.card ≤ t-4 := by
    intro hg
    have hgc : GC.card = 3 := by omega
    constructor
    · apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hi, ho⟩ := Finset.mem_filter.mp hi
      have hs := gate_false_target_sink T A.label S hS 0 x hi ho
      have hc := gate_sink_card_le_two T A.label S hS 0 x hs
      change GC.card ≤ 2 at hc
      omega
    · have hc := targets_card_with_three T A.label S hS 0 x A rfl hr hgc
      change TC.card ≤ t-4 at hc
      omega
  exact hcost.trans (coupled_weighted_bound_refined T0.card T1.card G0.card G1.card t
    (Z Ai Aj) (Y Gj Gi)
    (Z Gj Aj) (Y Gj Aj)
    ht hZA hYK hn1 hm0 hm hn hordinary hnzero htwo0 htwo1 hthree)
















end
end SensitivityRefined

/- Bundled unchanged module: GenericNQCoupledStage -/

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators
namespace SensitivityNQ
noncomputable section
variable {n : ℕ}
open SensitivityQ (DefectBound targetCost coupledCost aux_split_positive_zero coupled_pair_zero strict_split_pair_zero targetCost_mul coupledCost_mul)

def rawZeroCoupled (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  let a := Z (C.target i) (C.target j)
  let b := Z (C.gate j) (C.target j)
  let c := Y (C.gate j) (C.gate i)
  let e := Y (C.gate j) (C.target j)
  if j.val < 3 then k*(auxCost (C.aux i) (C.aux j) false*a)
  else if i.val < 3 then
    if C.aux i = 0 then 0
    else if C.tol j = 0 then
      max (a+(t-2)*Z (min (C.target i) (C.gate j)) (C.target j))
        ((t-1)*Z (min (C.target i) (C.gate j)) (C.target j))
    else targetCost (C.tol j) (v (C.tol j)) a
      (min a (Z (min (C.target i) (C.gate j)) (C.target j)))
  else if C.tol j = 0 then
    if C.tol i = 0 then
      max (max (max (max (a+c+(t-3)*b) (a+e+(t-2)*b)) (c+e+(t-3)*b)) (2*e+(t-2)*b)) (3*e+(t-4)*b)
    else max (a+(t-2)*b) ((t-1)*b)
  else if C.tol i = C.tol j then
    coupledCost (C.tol j) (v (C.tol j)) a b c e
  else targetCost (C.tol j) (v (C.tol j)) a b

theorem stage_zero_coupled {k t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T 2 t) (ht : 4 ≤ t)
    (v : ℕ → ℕ) (C : Recipe n) (hC : C.Valid)
    (hDefect : ∀ j : Fin n, 3 ≤ j.val → 0 < C.tol j →
      DefectBound T L.label (C.tol j) (v (C.tol j)))
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (Z Y : Fin n → Fin n → ℕ) (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (hc : Compatible C Z Y) :
    PairBound (stage T L.label C F) false (rawZeroCoupled k t v C Z Y) := by
  intro i j hij x hx hx'
  have hA := hC.1 hij
  by_cases hj : j.val < 3
  · have hi : i.val < 3 := by omega
    simp only [stage, if_pos hi, if_pos hj] at hx hx' ⊢
    simpa only [ite_true, ite_false, Nat.one_ne_zero, rawZeroCoupled, if_pos hj] using
      aux_pair_zero F hF (C.aux i) (C.aux j) (hC.2.1 i j hij hj)
        _ _ hA Z hZ x hx hx'
  · have hGB := (hC.2.2 j j le_rfl (by omega)).2.2
    simp only [stage, if_neg hj] at hx'
    by_cases hi : i.val < 3
    · simp only [stage, if_pos hi, if_neg hj] at hx ⊢
      by_cases hu : C.aux i = 0
      · simpa only [ite_true, ite_false, Nat.one_ne_zero, rawZeroCoupled, if_neg hj, if_pos hi, if_pos hu, hu] using
          aux_u_winner_zero T L.label F hF _ _ _ hA _ x (by simpa only [hu] using hx) hx'
      · by_cases hq : C.tol j = 0
        · simpa only [ite_true, ite_false, Nat.one_ne_zero, rawZeroCoupled, if_neg hj, if_pos hi, if_neg hu, if_pos hq, hq] using
            aux_ordinary_zero T L (C.aux i) F hF _ _ _ hA hGB Z hZ x hx
              (by simpa only [hq] using hx')
        · have hd := hDefect j (by omega) (by omega)
          simpa only [ite_true, ite_false, Nat.one_ne_zero, rawZeroCoupled, if_neg hj, if_pos hi, if_neg hu, if_neg hq] using
            aux_split_positive_zero T L.label hd (C.aux i) F hF _ _ _ hA hGB Z hZ x hx hx'
    · have hh := hC.2.2 i j hij (by omega)
      have hb := hc i j hij (by omega)
      simp only [stage, if_neg hi, if_neg hj] at hx ⊢
      by_cases hqj : C.tol j = 0
      · by_cases hqi : C.tol i = 0
        · simpa only [ite_true, ite_false, Nat.one_ne_zero, rawZeroCoupled, if_neg hj, if_neg hi, if_pos hqj, if_pos hqi,
            hqi, hqj, tolerant_zero_eq_mixed] using
            SensitivityRefined.mixed_pair_zero_coupled T L F hF (by decide) ht Z Y hZ hY
              (C.target i) (C.target j) (C.gate i) (C.gate j) hA hh.1 hh.2.2
              hb.1 hb.2 x (by simpa only [hqi, tolerant_zero_eq_mixed] using hx)
              (by simpa only [hqj, tolerant_zero_eq_mixed] using hx')
        · simpa only [ite_true, ite_false, Nat.one_ne_zero, rawZeroCoupled, if_neg hj, if_neg hi, if_pos hqj, if_neg hqi, hqj] using
            strict_ordinary_pair_zero T L F hF (by decide) Z hZ
              (C.target i) (C.target j) (C.gate i) (C.gate j) hA hh.1 hh.2.2
              (C.tol i) (by omega) x hx (by simpa only [hqj] using hx')
      · have hd := hDefect j (by omega) (by omega)
        by_cases he : C.tol i = C.tol j
        · simpa only [ite_true, ite_false, Nat.one_ne_zero, rawZeroCoupled, if_neg hj, if_neg hi, if_neg hqj, if_pos he, he] using
            coupled_pair_zero T L.label hd F hF (by decide) Z Y hZ hY
              (C.target i) (C.target j) (C.gate i) (C.gate j) hA hh.1 hh.2.2 hb.1 x
              (by simpa only [he] using hx) hx'
        · have hstrict : C.tol j < C.tol i := by omega
          simpa only [ite_true, ite_false, Nat.one_ne_zero, rawZeroCoupled, if_neg hj, if_neg hi, if_neg hqj, if_neg he] using
            strict_split_pair_zero T L.label (C.tol i) (C.tol j) hstrict hd F hF (by decide) Z hZ
              (C.target i) (C.target j) (C.gate i) (C.gate j) hA hh.1 hh.2.2 hb.1 x hx hx'

theorem rawZeroCoupled_mul (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (u : ℕ) (i j : Fin n) :
    rawZeroCoupled k t v C (fun i j => Z i j*u) (fun i j => Y i j*u) i j = rawZeroCoupled k t v C Z Y i j*u := by
  simp only [rawZeroCoupled]
  split_ifs <;> first | rfl | simp only [Nat.add_mul, Nat.mul_assoc, max_mul, Nat.zero_mul, ← min_mul, targetCost_mul, coupledCost_mul]

end
end SensitivityNQ
end



/- Component: Research.OrdinaryGuardGeometry -/
section
/-! Ordinary failed guards extend the target set without using another
defect.  This file contains the finite combinatorial part of the sharper
singleton-guard transfer; no new labeling-existence statement is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators

namespace SensitivityOrdinaryGuard
noncomputable section

variable {n k r : ℕ} {I : Type}

def ordinaryFailed (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin k) :=
  (failedGuards T label F G x i).filter fun j =>
    F A (recursiveChild x j (label i j)) = false

def ordinaryGuards (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  (tolerantGuards T label F A G q x).filter fun i =>
    (ordinaryFailed T label F A G x i).Nonempty

def ordinaryTotal (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) : ℕ :=
  ∑ i ∈ tolerantGuards T label F A G q x,
    (ordinaryFailed T label F A G x i).card

theorem ordinaryGuards_subset (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) :
    ordinaryGuards T label F A G q x ⊆ tolerantGuards T label F A G q x :=
  Finset.filter_subset _ _

theorem targets_ordinary_card {q v : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (hd : DefectBound T label q v)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (tolerantTargets T label F A G q x).card +
      (ordinaryGuards T label F A G q x).card < v := by
  let TC := tolerantTargets T label F A G q x
  let OG := ordinaryGuards T label F A G q x
  let GC := tolerantGuards T label F A G q x
  let B := failedGuards T label F G x
  let S := TC ∪ OG
  let tw := missingWitness F A x hr
  have ho : OG ⊆ GC := ordinaryGuards_subset T label F A G q x
  have hbad (i : Fin k) :
      S.filter (fun j => T.Adj i j ∧ label i j ≠ tw j) ⊆ B i := by
    intro j hj
    obtain ⟨hjS, hij, hne⟩ := Finset.mem_filter.mp hj
    apply (mem_failedGuards T label F G x i j).mpr
    refine ⟨hij, ?_⟩
    rcases Finset.mem_union.mp hjS with hjT | hjO
    · exact hF.accepts_of_le hGA
        (missingWitness_other_true F A x hr j
          (Finset.mem_filter.mp hjT).2.1 _ hne)
    · exact hF.accepts_of_le hGA
        ((missingTargets_empty F A x j).mp
          (Finset.mem_filter.mp (ho hjO)).2.1 _)
  have hlocal : ∀ i ∈ S,
      (S.filter fun j => T.Adj i j ∧ label i j ≠ tw j).card ≤ q := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiT | hiO
    · exact (Finset.card_le_card (hbad i)).trans
        (Finset.mem_filter.mp hiT).2.2
    · obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hiO).2
      obtain ⟨hjB, hjA⟩ := Finset.mem_filter.mp hj
      have hjnot : j ∉ S.filter
          (fun j => T.Adj i j ∧ label i j ≠ tw j) := by
        intro hjbad
        obtain ⟨hjS, _, hne⟩ := Finset.mem_filter.mp hjbad
        rcases Finset.mem_union.mp hjS with hjT | hjO
        · exact hne (missingWitness_unique F A x hr j
            (Finset.mem_filter.mp hjT).2.1 _ hjA)
        · have hon := (missingTargets_empty F A x j).mp
            (Finset.mem_filter.mp (ho hjO)).2.1 (label i j)
          simp only [hon, Bool.true_eq_false] at hjA
      have hproper : S.filter (fun j => T.Adj i j ∧ label i j ≠ tw j) ⊂ B i := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hbad i, ?_⟩
        intro he
        apply hjnot
        rw [he]
        exact hjB
      have hlt := Finset.card_lt_card hproper
      have hcount : (B i).card = q+1 := (Finset.mem_filter.mp (ho hiO)).2.2
      omega
  have hc := hd S tw hlocal
  have hdis : Disjoint TC OG := by
    apply Finset.disjoint_left.mpr
    intro i hiT hiO
    have hone : (missingTargets F A x i).card = 1 :=
      (Finset.mem_filter.mp hiT).2.1
    have hempty : missingTargets F A x i = ∅ :=
      (Finset.mem_filter.mp (ho hiO)).2.1
    simp only [hempty, Finset.card_empty] at hone
    omega
  change (TC ∪ OG).card < v at hc
  rw [Finset.card_union_of_disjoint hdis] at hc
  exact hc

theorem ordinary_sum_eq (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) :
    (∑ i ∈ ordinaryGuards T label F A G q x,
      (ordinaryFailed T label F A G x i).card) =
      ordinaryTotal T label F A G q x := by
  unfold ordinaryGuards ordinaryTotal
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hn : (ordinaryFailed T label F A G x i).Nonempty
  · simp only [if_pos hn]
  · have hz : ordinaryFailed T label F A G x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact hn ⟨j, hj⟩
    rw [if_neg hn, hz, Finset.card_empty]

theorem ordinary_arcs_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool)
    (S : Finset (Fin k)) (hS : S ⊆ tolerantGuards T label F A G q x) :
    (∑ i ∈ S, (ordinaryFailed T label F A G x i).card) ≤
      S.card*(q+1)-S.card.choose 2 := by
  let B := failedGuards T label F G x
  let O := ordinaryFailed T label F A G x
  have hinside (i : Fin k) : S.filter (T.Adj i) ⊆ B i := by
    intro j hj
    obtain ⟨hjS, hij⟩ := Finset.mem_filter.mp hj
    exact (mem_failedGuards T label F G x i j).mpr ⟨hij,
      hF.accepts_of_le hGA ((missingTargets_empty F A x j).mp
        (Finset.mem_filter.mp (hS hjS)).2.1 _)⟩
  have hdis (i : Fin k) : Disjoint (O i) (S.filter (T.Adj i)) := by
    apply Finset.disjoint_left.mpr
    intro j hjO hjS
    have hfalse : F A (recursiveChild x j (label i j)) = false :=
      (Finset.mem_filter.mp hjO).2
    have htrue : F A (recursiveChild x j (label i j)) = true :=
      (missingTargets_empty F A x j).mp
        (Finset.mem_filter.mp (hS (Finset.mem_filter.mp hjS).1)).2.1 _
    simp only [htrue, Bool.true_eq_false] at hfalse
  have hlocal : ∀ i ∈ S, (O i).card+(S.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    calc
      (O i).card+(S.filter (T.Adj i)).card =
          (O i ∪ S.filter (T.Adj i)).card :=
        (Finset.card_union_of_disjoint (hdis i)).symm
      _ ≤ (B i).card := Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (hinside i))
      _ = q+1 := (Finset.mem_filter.mp (hS hi)).2.2
  have hin : (∑ i ∈ S, (S.filter (T.Adj i)).card) = S.card.choose 2 := by
    rw [T.sum_outdegree_eq, T.card_internalEdges]
  have hsum : (∑ i ∈ S, (O i).card)+S.card.choose 2 ≤ S.card*(q+1) := by
    calc
      (∑ i ∈ S, (O i).card)+S.card.choose 2 =
          ∑ i ∈ S, ((O i).card+(S.filter (T.Adj i)).card) := by
        rw [Finset.sum_add_distrib, hin]
      _ ≤ ∑ _i ∈ S, (q+1) := Finset.sum_le_sum hlocal
      _ = S.card*(q+1) := by simp
  change (∑ i ∈ S, (O i).card) ≤ S.card*(q+1)-S.card.choose 2
  omega

theorem ordinary_counts (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) :
    let GC := tolerantGuards T label F A G q x
    let OG := ordinaryGuards T label F A G q x
    let L := ordinaryTotal T label F A G q x
    OG.card ≤ L ∧
      L ≤ min (OG.card*(q+1)-OG.card.choose 2)
        (GC.card*(q+1)-GC.card.choose 2) := by
  let GC := tolerantGuards T label F A G q x
  let OG := ordinaryGuards T label F A G q x
  let L := ordinaryTotal T label F A G q x
  have hsum := ordinary_sum_eq T label F A G q x
  change (∑ i ∈ OG, (ordinaryFailed T label F A G x i).card) = L at hsum
  constructor
  · calc
      OG.card = ∑ _i ∈ OG, 1 := by simp
      _ ≤ ∑ i ∈ OG, (ordinaryFailed T label F A G x i).card := by
        apply Finset.sum_le_sum
        intro i hi
        have hp := Finset.card_pos.mpr (Finset.mem_filter.mp hi).2
        omega
      _ = L := hsum
  · apply le_min
    · change L ≤ OG.card*(q+1)-OG.card.choose 2
      rw [← hsum]
      exact ordinary_arcs_bound T label F hF A G hGA q x OG
        (ordinaryGuards_subset T label F A G q x)
    · exact ordinary_arcs_bound T label F hF A G hGA q x GC (fun _ hi => hi)

theorem ordinary_weight_identity (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (c e : ℕ) :
    (∑ i ∈ tolerantGuards T label F A G q x,
      ∑ j ∈ failedGuards T label F G x i,
        if F A (recursiveChild x j (label i j)) = false then c else e) =
      ordinaryTotal T label F A G q x*c +
        ((tolerantGuards T label F A G q x).card*(q+1)-
          ordinaryTotal T label F A G q x)*e := by
  let GC := tolerantGuards T label F A G q x
  let B := failedGuards T label F G x
  let p := fun i j => F A (recursiveChild x j (label i j)) = false
  let L := ∑ i ∈ GC, ((B i).filter (p i)).card
  let J := ∑ i ∈ GC, ((B i).filter fun j => ¬p i j).card
  have hpartition : L+J = GC.card*(q+1) := by
    calc
      L+J = ∑ i ∈ GC, (((B i).filter (p i)).card+
          ((B i).filter fun j => ¬p i j).card) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ i ∈ GC, (B i).card := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.card_filter_add_card_filter_not (p i)
      _ = ∑ _i ∈ GC, (q+1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mem_filter.mp hi).2.2
      _ = GC.card*(q+1) := by simp
  have hJ : J = GC.card*(q+1)-L := by omega
  change (∑ i ∈ GC, ∑ j ∈ B i, if p i j then c else e) =
    L*c+(GC.card*(q+1)-L)*e
  calc
    _ = ∑ i ∈ GC, (((B i).filter (p i)).card*c+
        ((B i).filter fun j => ¬p i j).card*e) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ = L*c+J*e := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    _ = L*c+(GC.card*(q+1)-L)*e := by rw [hJ]

end
end SensitivityOrdinaryGuard
end



/- Component: Research.SourceGuardGeometry -/
section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators

namespace SensitivitySourceZero
noncomputable section

variable {n k r : ℕ} {I : Type}

/-- A source dominates all the other vertices of its finite set. -/
def HasSource (T : Tournament k) (S : Finset (Fin k)) : Prop :=
  ∃ s ∈ S, ∀ j ∈ S, j ≠ s → T.Adj s j

def SourceBound (T : Tournament k) (label : Fin k → Fin k → Fin r) (v : ℕ) : Prop :=
  ∀ (S : Finset (Fin k)) (colors : Fin k → Fin r), HasSource T S →
    (∀ i ∈ S, (S.filter fun j => T.Adj i j ∧ label i j ≠ colors j).card ≤ 0) →
    S.card < v

theorem target_no_edge_to_full_gate (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k)
    (hi : i ∈ tolerantTargets T label F A G 0 x)
    (hj : ∀ c, F G (recursiveChild x j c) = true) : ¬ T.Adj i j := by
  intro hij
  have hz : (failedGuards T label F G x i).card = 0 := by
    have hh := (Finset.mem_filter.mp hi).2.2
    omega
  have hempty := Finset.card_eq_zero.mp hz
  have hmem : j ∈ failedGuards T label F G x i :=
    (mem_failedGuards T label F G x i j).mpr ⟨hij, hj _⟩
  simpa only [hempty, Finset.notMem_empty] using hmem

theorem ordinary_card_le_one (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) :
    (SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x).card ≤ 1 := by
  let u := (SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x).card
  have hh := SensitivityOrdinaryGuard.ordinary_counts T label F hF A G hGA 0 x
  have hb : u ≤ u-u.choose 2 := by
    have ht := hh.1.trans (hh.2.trans (min_le_left _ _))
    simpa only [zero_add, Nat.mul_one] using ht
  have hc : u.choose 2 ≤ u*0 := by
    by_cases hu : u = 0
    · simp [hu]
    · omega
  exact source_card_arithmetic u 0 hc

theorem targets_ordinary_hasSource (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (hpos : (positiveTargets T label F A G 0 x hr).Nonempty ∨
      (SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x).Nonempty) :
    HasSource T (tolerantTargets T label F A G 0 x ∪
      SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x) := by
  let TC := tolerantTargets T label F A G 0 x
  let OG := SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x
  have hO : OG.card ≤ 1 := ordinary_card_le_one T label F hF A G hGA x
  have hfullO : ∀ s ∈ OG, ∀ c, F G (recursiveChild x s c) = true := by
    intro s hs c
    have hsG := SensitivityOrdinaryGuard.ordinaryGuards_subset T label F A G 0 x hs
    apply hF.accepts_of_le hGA
    exact (missingTargets_empty F A x s).mp (Finset.mem_filter.mp hsG).2.1 c
  by_cases hOG : OG.Nonempty
  · obtain ⟨s, hs⟩ := hOG
    refine ⟨s, Finset.mem_union_right _ hs, ?_⟩
    intro j hj hne
    rcases Finset.mem_union.mp hj with hjT | hjO
    · exact (T.adj_or_reverse (Ne.symm hne)).resolve_right
        (target_no_edge_to_full_gate T label F A G x j s hjT (hfullO s hs))
    · exact False.elim (hne ((Finset.card_le_one.mp hO) j hjO s hs))
  · have hP : (positiveTargets T label F A G 0 x hr).Nonempty := by
      rcases hpos with hp | ho
      · exact hp
      · exact False.elim (hOG ho)
    obtain ⟨s, hs⟩ := hP
    have hsT : s ∈ TC := (Finset.mem_filter.mp hs).1
    have hfull : ∀ c, F G (recursiveChild x s c) = true := by
      intro c
      by_cases hc : c = missingWitness F A x hr s
      · simpa only [hc] using (Finset.mem_filter.mp hs).2
      · exact hF.accepts_of_le hGA
          (missingWitness_other_true F A x hr s (Finset.mem_filter.mp hsT).2.1 c hc)
    refine ⟨s, Finset.mem_union_left _ hsT, ?_⟩
    intro j hj hne
    rcases Finset.mem_union.mp hj with hjT | hjO
    · exact (T.adj_or_reverse (Ne.symm hne)).resolve_right
        (target_no_edge_to_full_gate T label F A G x j s hjT hfull)
    · exact False.elim (hOG ⟨j, hjO⟩)

end
end SensitivitySourceZero

namespace SensitivityOrdinaryGuard
noncomputable section
variable {n k r : ℕ} {I : Type}

theorem targets_ordinary_local_defect {q : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    let S := tolerantTargets T label F A G q x ∪ ordinaryGuards T label F A G q x
    let tw := missingWitness F A x hr
    ∀ i ∈ S, (S.filter fun j => T.Adj i j ∧ label i j ≠ tw j).card ≤ q := by
  let TC := tolerantTargets T label F A G q x
  let OG := ordinaryGuards T label F A G q x
  let GC := tolerantGuards T label F A G q x
  let B := failedGuards T label F G x
  let S := TC ∪ OG
  let tw := missingWitness F A x hr
  have ho : OG ⊆ GC := ordinaryGuards_subset T label F A G q x
  have hbad (i : Fin k) :
      S.filter (fun j => T.Adj i j ∧ label i j ≠ tw j) ⊆ B i := by
    intro j hj
    obtain ⟨hjS, hij, hne⟩ := Finset.mem_filter.mp hj
    apply (mem_failedGuards T label F G x i j).mpr
    refine ⟨hij, ?_⟩
    rcases Finset.mem_union.mp hjS with hjT | hjO
    · exact hF.accepts_of_le hGA
        (missingWitness_other_true F A x hr j
          (Finset.mem_filter.mp hjT).2.1 _ hne)
    · exact hF.accepts_of_le hGA
        ((missingTargets_empty F A x j).mp
          (Finset.mem_filter.mp (ho hjO)).2.1 _)
  have hlocal : ∀ i ∈ S,
      (S.filter fun j => T.Adj i j ∧ label i j ≠ tw j).card ≤ q := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiT | hiO
    · exact (Finset.card_le_card (hbad i)).trans
        (Finset.mem_filter.mp hiT).2.2
    · obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hiO).2
      obtain ⟨hjB, hjA⟩ := Finset.mem_filter.mp hj
      have hjnot : j ∉ S.filter
          (fun j => T.Adj i j ∧ label i j ≠ tw j) := by
        intro hjbad
        obtain ⟨hjS, _, hne⟩ := Finset.mem_filter.mp hjbad
        rcases Finset.mem_union.mp hjS with hjT | hjO
        · exact hne (missingWitness_unique F A x hr j
            (Finset.mem_filter.mp hjT).2.1 _ hjA)
        · have hon := (missingTargets_empty F A x j).mp
            (Finset.mem_filter.mp (ho hjO)).2.1 (label i j)
          simp only [hon, Bool.true_eq_false] at hjA
      have hproper : S.filter (fun j => T.Adj i j ∧ label i j ≠ tw j) ⊂ B i := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hbad i, ?_⟩
        intro he
        apply hjnot
        rw [he]
        exact hjB
      have hlt := Finset.card_lt_card hproper
      have hcount : (B i).card = q+1 := (Finset.mem_filter.mp (ho hiO)).2.2
      omega
  exact hlocal

end
end SensitivityOrdinaryGuard

namespace SensitivitySourceZero
noncomputable section
variable {n k r : ℕ} {I : Type}

theorem targets_ordinary_card_source (T : Tournament k)
    (label : Fin k → Fin k → Fin r) {v : ℕ} (hd : SourceBound T label v)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (hpos : 0 < (positiveTargets T label F A G 0 x hr).card +
      (SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x).card) :
    (tolerantTargets T label F A G 0 x).card +
      (SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x).card < v := by
  let TC := tolerantTargets T label F A G 0 x
  let OG := SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x
  change 0 < (positiveTargets T label F A G 0 x hr).card + OG.card at hpos
  have hp : (positiveTargets T label F A G 0 x hr).Nonempty ∨ OG.Nonempty := by
    by_cases hp : 0 < (positiveTargets T label F A G 0 x hr).card
    · exact Or.inl (Finset.card_pos.mp hp)
    · exact Or.inr (Finset.card_pos.mp (by omega))
  have hs : HasSource T (TC ∪ OG) := targets_ordinary_hasSource T label F hF A G hGA x hr hp
  have hc := hd (TC ∪ OG) (missingWitness F A x hr) hs
    (SensitivityOrdinaryGuard.targets_ordinary_local_defect T label F hF A G hGA x hr)
  have hdis : Disjoint TC OG := by
    apply Finset.disjoint_left.mpr
    intro i hiT hiO
    have hone : (missingTargets F A x i).card = 1 := (Finset.mem_filter.mp hiT).2.1
    have hiG := SensitivityOrdinaryGuard.ordinaryGuards_subset T label F A G 0 x hiO
    have hempty : missingTargets F A x i = ∅ := (Finset.mem_filter.mp hiG).2.1
    simp only [hempty, Finset.card_empty] at hone
    omega
  rw [Finset.card_union_of_disjoint hdis] at hc
  exact hc

end
end SensitivitySourceZero
end



/- Component: Research.SourceGuardCandidates -/
section
/-! Even a nonordinary guard candidate supplies a source after deleting its
unique failed head.  With an internal guard edge no target head needs to be
deleted. These statements apply when positive-target and ordinary-guard
counts both vanish, too. -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators

namespace SensitivitySourceZero
noncomputable section

variable {n k r : ℕ} {I : Type}

theorem guard_not_target_zero (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ tolerantGuards T label F A G 0 x) :
    i ∉ tolerantTargets T label F A G 0 x := by
  intro hit
  have hone := (Finset.mem_filter.mp hit).2.1
  have hempty := (Finset.mem_filter.mp hi).2.1
  simp only [hempty, Finset.card_empty] at hone
  omega

theorem target_failedGuards_empty_zero (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ tolerantTargets T label F A G 0 x) :
    failedGuards T label F G x i = ∅ := by
  apply Finset.card_eq_zero.mp
  have hh := (Finset.mem_filter.mp hi).2.2
  omega

theorem guard_dominates_target_zero (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k)
    (hi : i ∈ tolerantGuards T label F A G 0 x)
    (hj : j ∈ tolerantTargets T label F A G 0 x) : T.Adj i j := by
  have hne : i ≠ j := by
    intro he
    subst j
    exact guard_not_target_zero T label F A G x i hi hj
  have hfull : ∀ c, F G (recursiveChild x i c) = true := by
    intro c
    exact hF.accepts_of_le hGA
      ((missingTargets_empty F A x i).mp (Finset.mem_filter.mp hi).2.1 c)
  exact (T.adj_or_reverse hne).resolve_right
    (target_no_edge_to_full_gate T label F A G x j i hj hfull)

/-- A full-target guard row can be inserted as a source into any subset
of target candidates avoiding its failed heads. -/
theorem guard_insert_targets_card_source (T : Tournament k)
    (label : Fin k → Fin k → Fin r) {w : ℕ} (hd : SourceBound T label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (i : Fin k) (hi : i ∈ tolerantGuards T label F A G 0 x)
    (J : Finset (Fin k)) (hJ : J ⊆ tolerantTargets T label F A G 0 x)
    (hpass : ∀ j ∈ J, j ∉ failedGuards T label F G x i) :
    (insert i J).card < w := by
  let S := insert i J
  let tw := missingWitness F A x hr
  have hfull : ∀ c, F G (recursiveChild x i c) = true := by
    intro c
    exact hF.accepts_of_le hGA
      ((missingTargets_empty F A x i).mp (Finset.mem_filter.mp hi).2.1 c)
  have hlabel (u v : Fin k)
      (hv : v ∈ tolerantTargets T label F A G 0 x)
      (huv : T.Adj u v) (hnot : v ∉ failedGuards T label F G x u) :
      label u v = tw v := by
    by_contra hne
    apply hnot
    apply (mem_failedGuards T label F G x u v).mpr
    exact ⟨huv, hF.accepts_of_le hGA
      (missingWitness_other_true F A x hr v (Finset.mem_filter.mp hv).2.1 _ hne)⟩
  have hs : HasSource T S := by
    refine ⟨i, Finset.mem_insert_self _ _, ?_⟩
    intro j hj hne
    have hjJ := (Finset.mem_insert.mp hj).resolve_left hne
    exact guard_dominates_target_zero T label F hF A G hGA x i j hi (hJ hjJ)
  have hcoherent : ∀ u ∈ S, ∀ v ∈ S, T.Adj u v → label u v = tw v := by
    intro u hu v hv huv
    have hvne : v ≠ i := by
      intro he
      subst v
      rcases Finset.mem_insert.mp hu with hui | huJ
      · exact T.ne_of_adj huv hui
      · exact (target_no_edge_to_full_gate T label F A G x u i (hJ huJ) hfull) huv
    have hvJ := (Finset.mem_insert.mp hv).resolve_left hvne
    rcases Finset.mem_insert.mp hu with hui | huJ
    · subst u
      exact hlabel i v (hJ hvJ) huv (hpass v hvJ)
    · apply hlabel u v (hJ hvJ) huv
      rw [target_failedGuards_empty_zero T label F A G x u (hJ huJ)]
      exact Finset.notMem_empty v
  have hlocal : ∀ u ∈ S,
      (S.filter fun v => T.Adj u v ∧ label u v ≠ tw v).card ≤ 0 := by
    intro u hu
    have hempty : S.filter (fun v => T.Adj u v ∧ label u v ≠ tw v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvS, huv, hne⟩ := Finset.mem_filter.mp hv
      exact hne (hcoherent u hu v hvS huv)
    rw [hempty]
    exact Nat.le_refl 0
  exact hd S tw hs hlocal

/-- A nonempty guard-candidate set bounds the targets by the conditional
source cutoff even if there are no positive or ordinary candidates. -/
theorem targets_card_source_of_guard_nonempty (T : Tournament k)
    (label : Fin k → Fin k → Fin r) {w : ℕ} (hd : SourceBound T label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (hGC : (tolerantGuards T label F A G 0 x).Nonempty) :
    (tolerantTargets T label F A G 0 x).card < w := by
  let TC := tolerantTargets T label F A G 0 x
  obtain ⟨i, hi⟩ := hGC
  have hcount : (failedGuards T label F G x i).card = 1 := by
    simpa only [Nat.zero_add] using (Finset.mem_filter.mp hi).2.2
  obtain ⟨g, hBg⟩ := Finset.card_eq_one.mp hcount
  have hpass : ∀ j ∈ TC.erase g, j ∉ failedGuards T label F G x i := by
    intro j hj
    rw [hBg]
    simpa only [Finset.mem_singleton] using (Finset.mem_erase.mp hj).1
  have hs := guard_insert_targets_card_source T label hd F hF A G hGA x hr i hi
    (TC.erase g) (fun _ hj => (Finset.mem_erase.mp hj).2) hpass
  have hinot : i ∉ TC.erase g := by
    intro hm
    exact guard_not_target_zero T label F A G x i hi (Finset.mem_erase.mp hm).2
  rw [Finset.card_insert_of_notMem hinot] at hs
  have hsub : TC ⊆ insert g (TC.erase g) := by
    intro j hj
    by_cases he : j = g
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨he, hj⟩))
  have hle : TC.card ≤ (TC.erase g).card+1 :=
    (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  exact hle.trans_lt hs

theorem targets_card_add_one_source_of_guard_edge (T : Tournament k)
    (label : Fin k → Fin k → Fin r) {w : ℕ} (hd : SourceBound T label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (i j : Fin k)
    (hi : i ∈ tolerantGuards T label F A G 0 x)
    (hj : j ∈ tolerantGuards T label F A G 0 x) (hij : T.Adj i j) :
    (tolerantTargets T label F A G 0 x).card+1 < w := by
  let TC := tolerantTargets T label F A G 0 x
  have hjB : j ∈ failedGuards T label F G x i := by
    apply (mem_failedGuards T label F G x i j).mpr
    exact ⟨hij, hF.accepts_of_le hGA
      ((missingTargets_empty F A x j).mp (Finset.mem_filter.mp hj).2.1 _)⟩
  have hcount : (failedGuards T label F G x i).card = 1 := by
    simpa only [Nat.zero_add] using (Finset.mem_filter.mp hi).2.2
  obtain ⟨g, hBg⟩ := Finset.card_eq_one.mp hcount
  have hjg : j = g := by
    rw [hBg, Finset.mem_singleton] at hjB
    exact hjB
  subst g
  have hpass : ∀ v ∈ TC, v ∉ failedGuards T label F G x i := by
    intro v hv
    rw [hBg, Finset.mem_singleton]
    intro he
    subst v
    exact guard_not_target_zero T label F A G x j hj hv
  have hs := guard_insert_targets_card_source T label hd F hF A G hGA x hr i hi TC
    (fun _ hv => hv) hpass
  have hinot : i ∉ TC := guard_not_target_zero T label F A G x i hi
  rw [Finset.card_insert_of_notMem hinot] at hs
  exact hs

/-- Two guard candidates supply an internal edge, whose failed head is not
a target candidate; consequently the inserted source gains one vertex. -/
theorem targets_card_add_one_source_of_two_guards (T : Tournament k)
    (label : Fin k → Fin k → Fin r) {w : ℕ} (hd : SourceBound T label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (hGC : 2 ≤ (tolerantGuards T label F A G 0 x).card) :
    (tolerantTargets T label F A G 0 x).card+1 < w := by
  obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp (by omega :
    1 < (tolerantGuards T label F A G 0 x).card)
  rcases T.adj_or_reverse hne with hij | hji
  · exact targets_card_add_one_source_of_guard_edge T label hd F hF A G hGA x hr i j hi hj hij
  · exact targets_card_add_one_source_of_guard_edge T label hd F hF A G hGA x hr j i hj hi hji

theorem ordinary_guard_no_edge_to_guard_zero (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (b a : Fin k)
    (hb : b ∈ SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x)
    (ha : a ∈ tolerantGuards T label F A G 0 x) : ¬T.Adj b a := by
  intro hba
  have hbR := SensitivityOrdinaryGuard.ordinaryGuards_subset T label F A G 0 x hb
  obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hb).2
  obtain ⟨hgB, hgA⟩ := Finset.mem_filter.mp hg
  have haB : a ∈ failedGuards T label F G x b := by
    apply (mem_failedGuards T label F G x b a).mpr
    exact ⟨hba, hF.accepts_of_le hGA
      ((missingTargets_empty F A x a).mp (Finset.mem_filter.mp ha).2.1 _)⟩
  have hle : (failedGuards T label F G x b).card ≤ 1 := by
    have hh := (Finset.mem_filter.mp hbR).2.2
    omega
  have hag : a = g := (Finset.card_le_one.mp hle) a haB g hgB
  subst a
  have ht := (missingTargets_empty F A x g).mp (Finset.mem_filter.mp ha).2.1 (label b g)
  simp only [ht, Bool.true_eq_false] at hgA

/-- An ordinary guard is coherent into every target head, including its
unique failed head when that head is a target candidate.  With another
guard pointing to it, both guards can therefore be added to the targets. -/
theorem targets_card_add_two_source_of_guard_and_ordinary (T : Tournament k)
    (label : Fin k → Fin k → Fin r) {w : ℕ} (hd : SourceBound T label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (a b : Fin k)
    (ha : a ∈ tolerantGuards T label F A G 0 x)
    (hb : b ∈ SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x)
    (hab : T.Adj a b) :
    (tolerantTargets T label F A G 0 x).card+2 < w := by
  let TC := tolerantTargets T label F A G 0 x
  let OG := SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x
  let S := insert a (insert b TC)
  let tw := missingWitness F A x hr
  let colors := fun j => if j = b then label a b else tw j
  have hbR := SensitivityOrdinaryGuard.ordinaryGuards_subset T label F A G 0 x hb
  have habne : a ≠ b := T.ne_of_adj hab
  have hnota : a ∉ TC := guard_not_target_zero T label F A G x a ha
  have hnotb : b ∉ TC := guard_not_target_zero T label F A G x b hbR
  have hfull (i : Fin k) (hi : i ∈ tolerantGuards T label F A G 0 x) :
      ∀ c, F G (recursiveChild x i c) = true := by
    intro c
    exact hF.accepts_of_le hGA
      ((missingTargets_empty F A x i).mp (Finset.mem_filter.mp hi).2.1 c)
  have hbB : b ∈ failedGuards T label F G x a :=
    (mem_failedGuards T label F G x a b).mpr ⟨hab, hfull b hbR _⟩
  have hpassa : ∀ v ∈ TC, v ∉ failedGuards T label F G x a := by
    intro v hv hvB
    have hle : (failedGuards T label F G x a).card ≤ 1 := by
      have hh := (Finset.mem_filter.mp ha).2.2
      omega
    have hvb : v = b := (Finset.card_le_one.mp hle) v hvB b hbB
    exact hnotb (hvb ▸ hv)
  have hlabela (v : Fin k) (hv : v ∈ TC) (hav : T.Adj a v) :
      label a v = tw v := by
    by_contra hne
    apply hpassa v hv
    exact (mem_failedGuards T label F G x a v).mpr ⟨hav, hF.accepts_of_le hGA
      (missingWitness_other_true F A x hr v (Finset.mem_filter.mp hv).2.1 _ hne)⟩
  have hbase : ∀ u ∈ TC ∪ OG, ∀ v ∈ TC ∪ OG,
      T.Adj u v → label u v = tw v := by
    intro u hu v hv huv
    by_contra hne
    have hlocal := SensitivityOrdinaryGuard.targets_ordinary_local_defect
      (q := 0) T label F hF A G hGA x hr u hu
    change ((TC ∪ OG).filter fun v => T.Adj u v ∧ label u v ≠ tw v).card ≤ 0 at hlocal
    have hz : ((TC ∪ OG).filter fun v => T.Adj u v ∧ label u v ≠ tw v).card = 0 := by
      omega
    have hm : v ∈ (TC ∪ OG).filter (fun v => T.Adj u v ∧ label u v ≠ tw v) :=
      Finset.mem_filter.mpr ⟨hv, huv, hne⟩
    have he := Finset.card_eq_zero.mp hz
    simp only [he, Finset.notMem_empty] at hm
  have hs : HasSource T S := by
    refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
    intro v hv hvne
    have hv' := (Finset.mem_insert.mp hv).resolve_left hvne
    rcases Finset.mem_insert.mp hv' with hvb | hvT
    · simpa only [hvb] using hab
    · exact guard_dominates_target_zero T label F hF A G hGA x a v ha hvT
  have hcoherent : ∀ u ∈ S, ∀ v ∈ S, T.Adj u v → label u v = colors v := by
    intro u hu v hv huv
    rcases Finset.mem_insert.mp hv with hva | hv'
    · subst v
      rcases Finset.mem_insert.mp hu with hua | hu'
      · exact False.elim (T.ne_of_adj huv hua)
      · rcases Finset.mem_insert.mp hu' with hub | huT
        · subst u
          exact False.elim (T.not_adj_reverse hab huv)
        · exact False.elim
            ((target_no_edge_to_full_gate T label F A G x u a huT (hfull a ha)) huv)
    · rcases Finset.mem_insert.mp hv' with hvb | hvT
      · subst v
        rcases Finset.mem_insert.mp hu with hua | hu'
        · subst u
          simp only [colors, if_pos rfl]
        · rcases Finset.mem_insert.mp hu' with hub | huT
          · exact False.elim (T.ne_of_adj huv hub)
          · exact False.elim
              ((target_no_edge_to_full_gate T label F A G x u b huT (hfull b hbR)) huv)
      · have hvne : v ≠ b := fun hvb => hnotb (hvb ▸ hvT)
        have hcol : colors v = tw v := by simp only [colors, if_neg hvne]
        rw [hcol]
        rcases Finset.mem_insert.mp hu with hua | hu'
        · subst u
          exact hlabela v hvT huv
        · rcases Finset.mem_insert.mp hu' with hub | huT
          · subst u
            exact hbase b (Finset.mem_union_right _ hb) v (Finset.mem_union_left _ hvT) huv
          · exact hbase u (Finset.mem_union_left _ huT) v (Finset.mem_union_left _ hvT) huv
  have hlocal : ∀ u ∈ S,
      (S.filter fun v => T.Adj u v ∧ label u v ≠ colors v).card ≤ 0 := by
    intro u hu
    have he : S.filter (fun v => T.Adj u v ∧ label u v ≠ colors v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvS, huv, hne⟩ := Finset.mem_filter.mp hv
      exact hne (hcoherent u hu v hvS huv)
    rw [he]
    exact Nat.le_refl 0
  have hc := hd S colors hs hlocal
  have hanot : a ∉ insert b TC := by
    intro hm
    rcases Finset.mem_insert.mp hm with hab' | haT
    · exact habne hab'
    · exact hnota haT
  change (insert a (insert b TC)).card < w at hc
  rw [Finset.card_insert_of_notMem hanot, Finset.card_insert_of_notMem hnotb] at hc
  omega

theorem targets_card_add_two_source_of_two_guards_ordinary (T : Tournament k)
    (label : Fin k → Fin k → Fin r) {w : ℕ} (hd : SourceBound T label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (hGC : 2 ≤ (tolerantGuards T label F A G 0 x).card)
    (hOG : (SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x).Nonempty) :
    (tolerantTargets T label F A G 0 x).card+2 < w := by
  obtain ⟨b, hb⟩ := hOG
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega :
    1 < (tolerantGuards T label F A G 0 x).card)
  have hex : ∃ a ∈ tolerantGuards T label F A G 0 x, a ≠ b := by
    by_cases hib : i = b
    · exact ⟨j, hj, fun hjb => hij (hib.trans hjb.symm)⟩
    · exact ⟨i, hi, hib⟩
  obtain ⟨a, ha, habne⟩ := hex
  have hab : T.Adj a b := (T.adj_or_reverse habne).resolve_right
    (ordinary_guard_no_edge_to_guard_zero T label F hF A G hGA x b a hb ha)
  exact targets_card_add_two_source_of_guard_and_ordinary T label hd F hF A G hGA x hr a b ha hb hab




end
end SensitivitySourceZero
end



/- Component: Research.SourceGuardBridge -/
section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical
namespace SensitivitySourceZero
noncomputable section
variable {n k r : ℕ} {I : Type}

theorem gateCandidates_twoPred (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) :
    gateCandidates T label (twoPred F G A) 0 x = tolerantGuards T label F A G 0 x := by
  ext i
  simp only [gateCandidates, tolerantGuards, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl




theorem positiveTargets_twoPred (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    positiveTargets T label F A G 0 x hr =
      (targetCandidates T label (twoPred F G A) 0 x).filter (fun i =>
        F G (recursiveChild x i (targetWitness (twoPred F G A) x hr i)) = true) := by
  unfold positiveTargets
  rw [tolerantTargets_zero]
  rfl

theorem gate_false_ordinary (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label (twoPred F G A) 0 x)
    (ho : F A (recursiveChild x (gateWitness T label (twoPred F G A) 0 x i)
      (label i (gateWitness T label (twoPred F G A) 0 x i))) = false) :
    i ∈ SensitivityOrdinaryGuard.ordinaryGuards T label F A G 0 x := by
  have hiG : i ∈ tolerantGuards T label F A G 0 x := by
    rw [← gateCandidates_twoPred]
    exact hi
  apply Finset.mem_filter.mpr
  refine ⟨hiG, ?_⟩
  let j := gateWitness T label (twoPred F G A) 0 x i
  have hs := gateWitness_spec T label (twoPred F G A) 0 x i hi
  refine ⟨j, Finset.mem_filter.mpr ⟨?_, ho⟩⟩
  apply (mem_failedGuards T label F G x i j).mpr
  exact ⟨hs.1, hs.2⟩

theorem targets_card_source_active (T : Tournament k)
    (label : Fin k → Fin k → Fin r) {w : ℕ} (hd : SourceBound T label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (hactive : 0 < (positiveTargets T label F A G 0 x hr).card +
      (tolerantGuards T label F A G 0 x).card) :
    (tolerantTargets T label F A G 0 x).card < w := by
  by_cases hp : 0 < (positiveTargets T label F A G 0 x hr).card
  · have hh := targets_ordinary_card_source T label hd F hF A G hGA x hr (by omega)
    omega
  · have hg : (tolerantGuards T label F A G 0 x).Nonempty := Finset.card_pos.mp (by omega)
    exact targets_card_source_of_guard_nonempty T label hd F hF A G hGA x hr hg

end
end SensitivitySourceZero
end



/- Component: Research.SourceGuardTriple -/
section
/-! Three zero-tolerance guard candidates have all their failed heads
inside the guard set.  Two of them may be added to the target candidates
to obtain a coherent set with a source. -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical

namespace SensitivitySourceZero
noncomputable section

variable {n k r : ℕ} {I : Type}

/-- A triple of guard candidates improves the conditional-source target
budget by two vertices, independently of the ordinary labeling cutoff. -/
theorem targets_card_add_two_source_of_three_guards (T : Tournament k)
    (label : Fin k → Fin k → Fin r) {w : ℕ} (hd : SourceBound T label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (hGC : (tolerantGuards T label F A G 0 x).card = 3) :
    (tolerantTargets T label F A G 0 x).card+2 < w := by
  let TC := tolerantTargets T label F A G 0 x
  let GC := tolerantGuards T label F A G 0 x
  change GC.card = 3 at hGC
  let P := twoPred F G A
  have hP : NestedFamily P := twoPred_nested F hF G A hGA
  have hGCeq : gateCandidates T label P 0 x = GC := by
    ext i
    simp only [gateCandidates, tolerantGuards, GC, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  have hgatecard : (gateCandidates T label P 0 x).card = 3 := by
    rw [hGCeq]
    exact hGC
  have hw (i : Fin k) (hi : i ∈ GC) : gateWitness T label P 0 x i ∈ GC := by
    rw [← hGCeq] at hi ⊢
    exact gate_card_three_witness_mem T label P hP 0 x hgatecard hi
  have hpass (i : Fin k) (hi : i ∈ GC) (v : Fin k) (hv : v ∈ TC) :
      v ∉ failedGuards T label F G x i := by
    intro hvB
    obtain ⟨hiv, hon⟩ := (mem_failedGuards T label F G x i v).mp hvB
    have hi' : i ∈ gateCandidates T label P 0 x := by rw [hGCeq]; exact hi
    have he : v = gateWitness T label P 0 x i :=
      gateWitness_unique T label P 0 x i hi' v hiv hon
    have hvG : v ∈ GC := by rw [he]; exact hw i hi
    exact guard_not_target_zero T label F A G x v hvG hv
  have hnonempty : GC.Nonempty := Finset.card_pos.mp (by change 0 < GC.card; omega)
  obtain ⟨a, ha⟩ := hnonempty
  let b := gateWitness T label P 0 x a
  have hb : b ∈ GC := hw a ha
  have ha' : a ∈ gateCandidates T label P 0 x := by rw [hGCeq]; exact ha
  have hab : T.Adj a b := (gateWitness_spec T label P 0 x a ha').1
  let S := insert a (insert b TC)
  let tw := missingWitness F A x hr
  let colors := fun j => if j = b then label a b else tw j
  have habne : a ≠ b := T.ne_of_adj hab
  have hnota : a ∉ TC := guard_not_target_zero T label F A G x a ha
  have hnotb : b ∉ TC := guard_not_target_zero T label F A G x b hb
  have hfull (i : Fin k) (hi : i ∈ GC) : ∀ c, F G (recursiveChild x i c) = true := by
    intro c
    exact hF.accepts_of_le hGA
      ((missingTargets_empty F A x i).mp (Finset.mem_filter.mp hi).2.1 c)
  have hlabel (u v : Fin k) (hv : v ∈ TC) (huv : T.Adj u v)
      (hnot : v ∉ failedGuards T label F G x u) : label u v = tw v := by
    by_contra hne
    apply hnot
    exact (mem_failedGuards T label F G x u v).mpr ⟨huv, hF.accepts_of_le hGA
      (missingWitness_other_true F A x hr v (Finset.mem_filter.mp hv).2.1 _ hne)⟩
  have hs : HasSource T S := by
    refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
    intro v hv hvne
    have hv' := (Finset.mem_insert.mp hv).resolve_left hvne
    rcases Finset.mem_insert.mp hv' with hvb | hvT
    · simpa only [hvb] using hab
    · exact guard_dominates_target_zero T label F hF A G hGA x a v ha hvT
  have hcoherent : ∀ u ∈ S, ∀ v ∈ S, T.Adj u v → label u v = colors v := by
    intro u hu v hv huv
    rcases Finset.mem_insert.mp hv with hva | hv'
    · subst v
      rcases Finset.mem_insert.mp hu with hua | hu'
      · exact False.elim (T.ne_of_adj huv hua)
      · rcases Finset.mem_insert.mp hu' with hub | huT
        · subst u
          exact False.elim (T.not_adj_reverse hab huv)
        · exact False.elim
            ((target_no_edge_to_full_gate T label F A G x u a huT (hfull a ha)) huv)
    · rcases Finset.mem_insert.mp hv' with hvb | hvT
      · subst v
        rcases Finset.mem_insert.mp hu with hua | hu'
        · subst u
          simp only [colors, if_pos rfl]
        · rcases Finset.mem_insert.mp hu' with hub | huT
          · exact False.elim (T.ne_of_adj huv hub)
          · exact False.elim
              ((target_no_edge_to_full_gate T label F A G x u b huT (hfull b hb)) huv)
      · have hvne : v ≠ b := fun hvb => hnotb (hvb ▸ hvT)
        have hcol : colors v = tw v := by simp only [colors, if_neg hvne]
        rw [hcol]
        rcases Finset.mem_insert.mp hu with hua | hu'
        · subst u
          exact hlabel a v hvT huv (hpass a ha v hvT)
        · rcases Finset.mem_insert.mp hu' with hub | huT
          · subst u
            exact hlabel b v hvT huv (hpass b hb v hvT)
          · apply hlabel u v hvT huv
            rw [target_failedGuards_empty_zero T label F A G x u huT]
            exact Finset.notMem_empty v
  have hlocal : ∀ u ∈ S,
      (S.filter fun v => T.Adj u v ∧ label u v ≠ colors v).card ≤ 0 := by
    intro u hu
    have he : S.filter (fun v => T.Adj u v ∧ label u v ≠ colors v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvS, huv, hne⟩ := Finset.mem_filter.mp hv
      exact hne (hcoherent u hu v hvS huv)
    rw [he]
    exact Nat.le_refl 0
  have hc := hd S colors hs hlocal
  have hanot : a ∉ insert b TC := by
    intro hm
    rcases Finset.mem_insert.mp hm with hab' | haT
    · exact habne hab'
    · exact hnota haT
  change (insert a (insert b TC)).card < w at hc
  rw [Finset.card_insert_of_notMem hanot, Finset.card_insert_of_notMem hnotb] at hc
  omega

end
end SensitivitySourceZero
end



/- Component: Research.OrdinaryGuardArithmetic -/
section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open scoped Classical

namespace SensitivityOrdinaryGuard
noncomputable section

def ordinaryLimit (q m u : ℕ) : ℕ :=
  min (u*(q+1)-u.choose 2) (m*(q+1)-m.choose 2)

def ordinaryCost (q v a b c e : ℕ) : ℕ :=
  (Finset.range (2*q+2)).sup fun n =>
    (Finset.range (2*q+4)).sup fun m =>
      (Finset.range (2*q+4)).sup fun u =>
        if (n+m).choose 2 ≤ q*n+(q+1)*m ∧
            n+u ≤ v-1 ∧ u ≤ m ∧ u ≤ ordinaryLimit q m u then
          n*a+(v-1-u-n)*b+ordinaryLimit q m u*c+
            (m*(q+1)-ordinaryLimit q m u)*e
        else 0

theorem split_charge_mono (N L U c e : ℕ)
    (hLU : L ≤ U) (hUN : U ≤ N) (hec : e ≤ c) :
    L*c+(N-L)*e ≤ U*c+(N-U)*e := by
  have heq (l : ℕ) (hl : l ≤ N) :
      l*c+(N-l)*e = N*e+l*(c-e) := by
    calc
      l*c+(N-l)*e = l*((c-e)+e)+(N-l)*e := by
        rw [Nat.sub_add_cancel hec]
      _ = l*(c-e)+(l+(N-l))*e := by ring
      _ = N*e+l*(c-e) := by
        have hh : l+(N-l) = N := by omega
        rw [hh]
        ring
  rw [heq L (hLU.trans hUN), heq U hUN]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (c-e) hLU) _

theorem ordinaryLimit_le_total (q m u : ℕ) :
    ordinaryLimit q m u ≤ m*(q+1) :=
  (min_le_right _ _).trans (Nat.sub_le _ _)

theorem charge_le_ordinaryCost (q v a b c e n m u L : ℕ)
    (hn : n ≤ 2*q+1) (hm : m ≤ 2*q+3) (hu : u ≤ m)
    (hc : (n+m).choose 2 ≤ q*n+(q+1)*m)
    (hnu : n+u ≤ v-1) (huL : u ≤ L)
    (hL : L ≤ ordinaryLimit q m u) (hec : e ≤ c) :
    n*a+(v-1-u-n)*b+L*c+(m*(q+1)-L)*e ≤
      ordinaryCost q v a b c e := by
  have hh := split_charge_mono (m*(q+1)) L (ordinaryLimit q m u) c e
    hL (ordinaryLimit_le_total q m u) hec
  have hcharge : n*a+(v-1-u-n)*b+L*c+(m*(q+1)-L)*e ≤
      n*a+(v-1-u-n)*b+ordinaryLimit q m u*c+
        (m*(q+1)-ordinaryLimit q m u)*e := by
    simpa only [Nat.add_assoc] using Nat.add_le_add_left hh (n*a+(v-1-u-n)*b)
  apply hcharge.trans
  unfold ordinaryCost
  apply Finset.le_sup_of_le (b := n) (Finset.mem_range.mpr (by omega))
  apply Finset.le_sup_of_le (b := m) (Finset.mem_range.mpr (by omega))
  apply Finset.le_sup_of_le (b := u) (Finset.mem_range.mpr (by omega))
  rw [if_pos ⟨hc, hnu, hu, huL.trans hL⟩]

theorem ordinaryCost_mul (q v a b c e w : ℕ) :
    ordinaryCost q v (a*w) (b*w) (c*w) (e*w) =
      ordinaryCost q v a b c e*w := by
  unfold ordinaryCost
  rw [Finset.sup_mul₀]
  congr 1
  funext n
  rw [Finset.sup_mul₀]
  congr 1
  funext m
  rw [Finset.sup_mul₀]
  congr 1
  funext u
  split_ifs <;> simp only [Nat.zero_mul, Nat.add_mul, Nat.mul_assoc]

end
end SensitivityOrdinaryGuard
end



/- Component: Research.SourceGuardArithmetic -/
section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open scoped Classical

namespace SensitivitySourceZero
noncomputable section

def effectiveCutoff (v w n u : ℕ) : ℕ := if n+u = 0 then v else w

def sourceCost (v w a b c e : ℕ) : ℕ :=
  (Finset.range 2).sup fun n =>
    (Finset.range 4).sup fun m =>
      (Finset.range 4).sup fun u =>
        if (n+m).choose 2 ≤ m ∧ n+u ≤ effectiveCutoff v w n u-1 ∧
            u ≤ m ∧ u ≤ SensitivityOrdinaryGuard.ordinaryLimit 0 m u then
          n*a+(effectiveCutoff v w n u-1-u-n)*b+
            SensitivityOrdinaryGuard.ordinaryLimit 0 m u*c+
            (m-SensitivityOrdinaryGuard.ordinaryLimit 0 m u)*e
        else 0

theorem charge_le_sourceCost (v w a b c e n m u L : ℕ)
    (hn : n ≤ 1) (hm : m ≤ 3) (hu : u ≤ m)
    (hc : (n+m).choose 2 ≤ m)
    (hnu : n+u ≤ effectiveCutoff v w n u-1) (huL : u ≤ L)
    (hL : L ≤ SensitivityOrdinaryGuard.ordinaryLimit 0 m u) (hec : e ≤ c) :
    n*a+(effectiveCutoff v w n u-1-u-n)*b+L*c+(m-L)*e ≤
      sourceCost v w a b c e := by
  have hUN : SensitivityOrdinaryGuard.ordinaryLimit 0 m u ≤ m := by
    simpa only [zero_add, Nat.mul_one] using
      SensitivityOrdinaryGuard.ordinaryLimit_le_total 0 m u
  have hh := SensitivityOrdinaryGuard.split_charge_mono m L
    (SensitivityOrdinaryGuard.ordinaryLimit 0 m u) c e hL hUN hec
  have hcharge : n*a+(effectiveCutoff v w n u-1-u-n)*b+L*c+(m-L)*e ≤
      n*a+(effectiveCutoff v w n u-1-u-n)*b+
        SensitivityOrdinaryGuard.ordinaryLimit 0 m u*c+
        (m-SensitivityOrdinaryGuard.ordinaryLimit 0 m u)*e := by
    simpa only [Nat.add_assoc] using Nat.add_le_add_left hh
      (n*a+(effectiveCutoff v w n u-1-u-n)*b)
  apply hcharge.trans
  unfold sourceCost
  apply Finset.le_sup_of_le (b := n) (Finset.mem_range.mpr (by omega))
  apply Finset.le_sup_of_le (b := m) (Finset.mem_range.mpr (by omega))
  apply Finset.le_sup_of_le (b := u) (Finset.mem_range.mpr (by omega))
  rw [if_pos ⟨hc, hnu, hu, huL.trans hL⟩]

theorem sourceCost_mul (v w a b c e s : ℕ) :
    sourceCost v w (a*s) (b*s) (c*s) (e*s) = sourceCost v w a b c e*s := by
  unfold sourceCost
  rw [Finset.sup_mul₀]
  congr 1
  funext n
  rw [Finset.sup_mul₀]
  congr 1
  funext m
  rw [Finset.sup_mul₀]
  congr 1
  funext u
  split_ifs <;> simp only [Nat.zero_mul, Nat.add_mul, Nat.mul_assoc]

end
end SensitivitySourceZero
end



/- Component: Research.SourceStrictArithmetic -/
section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open scoped Classical
namespace SensitivitySourceZero
noncomputable section

theorem active_weighted_bound (n0 n1 m0 m1 w A B J K : ℕ)
    (ht : 4 ≤ w) (hJA : J ≤ A) (hKB : K ≤ B)
    (hn1 : n1 ≤ 1) (hm0 : m0 ≤ 1) (hm : m0 + m1 ≤ 3)
    (hn : n0 + n1 ≤ w - 1)
    (hordinary : 0 < m0 → n0 + n1 ≤ w - 2)
    (hnzero : 2 ≤ m0 + m1 → n1 = 0)
    (htwo0 : m0 + m1 = 2 → m0 = 0 → n0 ≤ w - 2)
    (htwo1 : m0 + m1 = 2 → m0 = 1 → n0 ≤ w - 3)
    (hthree : m0 + m1 = 3 → m0 = 0 ∧ n0 ≤ w - 3) :
    n1 * A + n0 * J + m0 * B + m1 * K ≤
      max (max (max (max (A+B+(w-3)*J) (A+K+(w-2)*J))
        (B+K+(w-3)*J)) (2*K+(w-2)*J)) (3*K+(w-3)*J) := by
  let R := max (max (max (max (A+B+(w-3)*J) (A+K+(w-2)*J))
      (B+K+(w-3)*J)) (2*K+(w-2)*J)) (3*K+(w-3)*J)
  have hR0 : A+B+(w-3)*J ≤ R :=
    (le_max_left _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans (le_max_left _ _)))
  have hR1 : A+K+(w-2)*J ≤ R :=
    (le_max_right _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans (le_max_left _ _)))
  have hR2 : B+K+(w-3)*J ≤ R :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hR3 : 2*K+(w-2)*J ≤ R :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hR4 : 3*K+(w-3)*J ≤ R := le_max_right _ _
  change _ ≤ R
  by_cases hsmall : m0 + m1 ≤ 1
  · by_cases hmzero : m0 = 0
    · have hm1 : m1 ≤ 1 := by omega
      have hgate : m0*B+m1*K ≤ K := by
        simp only [hmzero, Nat.zero_mul, Nat.zero_add]
        simpa using Nat.mul_le_mul_right K hm1
      have htargets : n1*A+n0*J ≤ A+(w-2)*J := by
        have ht2 : w-2+1 = w-1 := _root_.SensitivityProofArithmetic.sub_two_add_one_explicit w (Nat.le_trans (by decide : 2 ≤ 4) ht)
        interval_cases n1
        · have hmul := Nat.mul_le_mul_right J hn
          simp only [Nat.add_zero, Nat.zero_mul] at *
          rw [← ht2, Nat.add_mul, Nat.one_mul] at hmul
          omega
        · have hbound : n0 ≤ w-2 := by omega
          have hmul := Nat.mul_le_mul_right J hbound
          simp only [Nat.one_mul]
          omega
      exact (show n1*A+n0*J+m0*B+m1*K ≤ A+K+(w-2)*J by omega).trans hR1
    · have hmzero : m0 = 1 := by omega
      have hmone : m1 = 0 := by omega
      have hn' : n0 + n1 ≤ w-2 := hordinary (by omega)
      have htargets : n1*A+n0*J ≤ A+(w-3)*J := by
        have ht3 : w-3+1 = w-2 := by omega
        interval_cases n1
        · have hmul := Nat.mul_le_mul_right J hn'
          simp only [Nat.add_zero, Nat.zero_mul] at *
          rw [← ht3, Nat.add_mul, Nat.one_mul] at hmul
          omega
        · have hbound : n0 ≤ w-3 := by omega
          have hmul := Nat.mul_le_mul_right J hbound
          simp only [Nat.one_mul]
          omega
      exact (show n1*A+n0*J+m0*B+m1*K ≤ A+B+(w-3)*J by
        simp only [hmzero, hmone, Nat.one_mul, Nat.zero_mul]; omega).trans hR0
  · have hnzero' := hnzero (by omega)
    subst n1
    by_cases htwo : m0+m1=2
    · interval_cases m0
      · have hbound := htwo0 htwo rfl
        have hm1 : m1 = 2 := by omega
        subst m1
        have hmul := Nat.mul_le_mul_right J hbound
        exact (show 0*A+n0*J+0*B+2*K ≤ 2*K+(w-2)*J by omega).trans hR3
      · have hbound := htwo1 htwo rfl
        have hm1 : m1 = 1 := by omega
        subst m1
        have hmul := Nat.mul_le_mul_right J hbound
        exact (show 0*A+n0*J+1*B+1*K ≤ B+K+(w-3)*J by omega).trans hR2
    · have hsum : m0+m1=3 := by omega
      obtain ⟨hmzero, hbound⟩ := hthree hsum
      subst m0
      have hm1 : m1=3 := by omega
      subst m1
      have hmul := Nat.mul_le_mul_right J hbound
      exact (show 0*A+n0*J+0*B+3*K ≤ 3*K+(w-3)*J by omega).trans hR4


def strictSourceCost (t w a b c e : ℕ) : ℕ :=
  max (max (max (max (max (a+c+(w-3)*b) (a+e+(w-2)*b))
    (c+e+(w-3)*b)) (2*e+(w-2)*b)) (3*e+(w-3)*b)) ((t-1)*b)

theorem target_source_arithmetic (n0 n1 t w a b : ℕ) (hn1 : n1 ≤ 1)
    (hn : n0+n1 ≤ t-1) (hsource : 0 < n1 → n0+n1 ≤ w-1) :
    n1*a+n0*b ≤ max (a+(w-2)*b) ((t-1)*b) := by
  interval_cases n1
  · have hh := Nat.mul_le_mul_right b hn
    simp only [Nat.add_zero, Nat.zero_mul, Nat.zero_add] at *
    exact hh.trans (le_max_right _ _)
  · have hs := hsource (by decide)
    have hbound : n0 ≤ w-2 := by omega
    have hh := Nat.mul_le_mul_right b hbound
    exact (show 1*a+n0*b ≤ a+(w-2)*b by omega).trans (le_max_left _ _)

theorem strict_weighted_bound (n0 n1 m0 m1 t w A B J K : ℕ)
    (hw : 4 ≤ w) (hJA : J ≤ A) (hKB : K ≤ B)
    (hn1 : n1 ≤ 1) (hm0 : m0 ≤ 1) (hm : m0+m1 ≤ 3)
    (hn : n0+n1 ≤ t-1)
    (hsource : 0 < n1+m0+m1 → n0+n1 ≤ w-1)
    (hordinary : 0 < m0 → n0+n1 ≤ w-2)
    (hnzero : 2 ≤ m0+m1 → n1 = 0)
    (htwo0 : m0+m1 = 2 → m0 = 0 → n0 ≤ w-2)
    (htwo1 : m0+m1 = 2 → m0 = 1 → n0 ≤ w-3)
    (hthree : m0+m1 = 3 → m0 = 0 ∧ n0 ≤ w-3) :
    n1*A+n0*J+m0*B+m1*K ≤ strictSourceCost t w A J B K := by
  by_cases hactive : 0 < n1+m0+m1
  · exact (active_weighted_bound n0 n1 m0 m1 w A B J K hw hJA hKB
      hn1 hm0 hm (hsource hactive) hordinary hnzero htwo0 htwo1 hthree).trans
        (le_max_left _ _)
  · have hnzero' : n1 = 0 := by omega
    have hmzero' : m0 = 0 := by omega
    have hmone' : m1 = 0 := by omega
    have hh : n0*J ≤ (t-1)*J := Nat.mul_le_mul_right J (by omega)
    have hb : n1*A+n0*J+m0*B+m1*K ≤ (t-1)*J := by
      simpa only [hnzero', hmzero', hmone', Nat.zero_mul, zero_add, add_zero] using hh
    exact hb.trans (le_max_right _ _)

theorem strictSourceCost_mul (t w a b c e s : ℕ) :
    strictSourceCost t w (a*s) (b*s) (c*s) (e*s) =
      strictSourceCost t w a b c e*s := by
  simp only [strictSourceCost, Nat.add_mul, Nat.mul_assoc, max_mul]

end
end SensitivitySourceZero
end



/- Component: Research.OrdinaryGuardStage -/
section
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators

namespace SensitivityOrdinaryGuard
noncomputable section

theorem ordinary_pair_zero {n k r q v : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r) (hDefect : DefectBound T label q v)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (Z Y : Fin n → Fin n → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hGA : Gi ≤ Ai)
    (hZle : Z Gj Aj ≤ Z Ai Aj) (hYle : Y Gj Aj ≤ Y Gj Gi)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T label F Ai Gi q x = false)
    (hx' : tolerantFamily T label F Aj Gj q x = false) :
    jointSensitivityAt (tolerantFamily T label F Ai Gi q)
      (tolerantFamily T label F Aj Gj q) x ≤
      ordinaryCost q v (Z Ai Aj) (Z Gj Aj) (Y Gj Gi) (Y Gj Aj) := by
  let TC := tolerantTargets T label F Aj Gj q x
  let GC := tolerantGuards T label F Aj Gj q x
  let OG := ordinaryGuards T label F Aj Gj q x
  let L := ordinaryTotal T label F Aj Gj q x
  let P := positiveTargets T label F Aj Gj q x hr
  let tw := missingWitness F Aj x hr
  let B := failedGuards T label F Gj x
  let U := splitTargetChanges F Ai Aj Gj Gj x TC tw
  let V := GC.biUnion fun i => (B i).biUnion fun j =>
    if F Aj (recursiveChild x j (label i j)) = false
      then childJointChanges F Gj Gi x j (label i j)
      else childJointChanges F Gj Aj x j (label i j)
  have hGJA : Gj ≤ Aj := hG.trans (hGA.trans hA)
  have hweakguard : ∀ i ∈ GC, ∀ j ∈ B i,
      F Gi (recursiveChild x j (label i j)) = true := by
    intro i hi j hj
    have he := tolerant_guard_sets_eq T label F hF Ai Aj Gi Gj hA hG x q hx hi
    have hj' : j ∈ failedGuards T label F Gi x i := by rw [he]; exact hj
    exact ((mem_failedGuards T label F Gi x i j).mp hj').2
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T label F Ai Gi q (flip x {p}) ≠ tolerantFamily T label F Ai Gi q x ∧
      tolerantFamily T label F Aj Gj q (flip x {p}) ≠ tolerantFamily T label F Aj Gj q x) ⊆
      U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)}) = true := by
      cases hy : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)})
      · exact False.elim (hc.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi⟩ := (tolerantFamily_true T label F Aj Gj q _).mp hon
    have hoff := (tolerantFamily_false T label F Aj Gj q x).mp hx' i
    rcases tolerant_repair_cases T label F Aj Gj q x i j c a hoff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, hcl, hgon, hgoff⟩
    · subst j
      have hcw := missingWitness_unique F Aj x hr i (Finset.mem_filter.mp hit).2.1 c htoff
      have hwo : F Ai (recursiveChild x i c) = false := by
        rw [hcw]
        exact tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
          (le_refl q) hr hx hit
      have hwn := hF.accepts_of_le hA hton
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
          F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
        simp [hwo, hwn, htoff, hton]
      by_cases hgo : F Gj (recursiveChild x i (tw i)) = true
      · rw [if_pos hgo]
        simpa [childJointChanges, tw, hcw] using hn
      · rw [if_neg hgo]
        apply Finset.mem_inter.mpr
        constructor
        · simpa [childJointChanges, tw, hcw] using hn
        · have hgoff : F Gj (recursiveChild x i c) = false := by
            simpa only [tw, ← hcw, Bool.not_eq_true] using hgo
          have hgn := hF.accepts_of_le hGJA hton
          have hn0 : F Gj (flip (recursiveChild x i c) {a}) ≠ F Gj (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
            simp [hgoff, hgn, htoff, hton]
          simpa [childJointChanges, tw, hcw] using hn0
    · subst c
      have hj : j ∈ B i := (mem_failedGuards T label F Gj x i j).mpr ⟨hij, hgon⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hig, Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩⟩
      by_cases hfalse : F Aj (recursiveChild x j (label i j)) = false
      · rw [if_pos hfalse]
        have hwo := hweakguard i hig j hj
        have hwf := hF.rejects_of_le hG hgoff
        have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gj (recursiveChild x j (label i j)) ∧
            F Gi (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gi (recursiveChild x j (label i j)) := by simp [hgon, hgoff, hwo, hwf]
        simpa [childJointChanges] using hn
      · rw [if_neg hfalse]
        have hto : F Aj (recursiveChild x j (label i j)) = true := by
          cases hh : F Aj (recursiveChild x j (label i j)) <;> simp_all
        have htf := hF.rejects_of_le hGJA hgoff
        have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gj (recursiveChild x j (label i j)) ∧
            F Aj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Aj (recursiveChild x j (label i j)) := by simp [hgon, hgoff, hto, htf]
        simpa [childJointChanges] using hn
  have hTU : TC.card+OG.card < v :=
    targets_ordinary_card T label hDefect F hF Aj Gj hGJA x hr
  have hTC : TC.card ≤ v-1-OG.card := by omega
  have hP : P.card ≤ TC.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hU : U.card ≤ P.card*Z Ai Aj+(v-1-OG.card-P.card)*Z Gj Aj := by
    have hh := splitTargetChanges_card_count F Ai Aj Gj Gj hA hGJA Z hZ x TC tw
      (fun i hi => tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
        (le_refl q) hr hx hi)
      (fun i hi => missingWitness_false F Aj x hr i (Finset.mem_filter.mp hi).2.1)
      (fun i hi hn => Bool.eq_false_iff.mpr hn)
    have hU0 : U.card ≤ P.card*Z Ai Aj+(TC.card-P.card)*Z Gj Aj := by
      simpa only [U, P, positiveTargets, TC, tw, min_eq_right hZle] using hh
    exact hU0.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hTC P.card)) _)
  have hV : V.card ≤ L*Y Gj Gi+(GC.card*(q+1)-L)*Y Gj Aj := by
    apply le_trans Finset.card_biUnion_le
    apply le_trans (Finset.sum_le_sum (fun i hi => Finset.card_biUnion_le))
    apply le_trans (Finset.sum_le_sum ?_)
      (ordinary_weight_identity T label F Aj Gj q x (Y Gj Gi) (Y Gj Aj)).le
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hgo := ((mem_failedGuards T label F Gj x i j).mp hj).2
    by_cases hfalse : F Aj (recursiveChild x j (label i j)) = false
    · rw [if_pos hfalse, if_pos hfalse, childJointChanges_card]
      exact hY _ _ hG _ hgo (hweakguard i hi j hj)
    · rw [if_neg hfalse, if_neg hfalse, childJointChanges_card]
      have hto : F Aj (recursiveChild x j (label i j)) = true := by
        cases hh : F Aj (recursiveChild x j (label i j)) <;> simp_all
      exact hY _ _ hGJA _ hgo hto
  have hcounts := ordinary_counts T label F hF Aj Gj hGJA q x
  change OG.card ≤ L ∧ L ≤ ordinaryLimit q GC.card OG.card at hcounts
  have hnum := charge_le_ordinaryCost q v (Z Ai Aj) (Z Gj Aj) (Y Gj Gi) (Y Gj Aj)
    P.card GC.card OG.card L
    (positiveTargets_card T label F hF Aj Gj hGJA q x hr)
    (guards_card T label F hF Aj Gj hGJA q x)
    (Finset.card_le_card (ordinaryGuards_subset T label F Aj Gj q x))
    (positiveTargets_guards_coupling T label F hF Aj Gj hGJA q x hr)
    (by omega) hcounts.1 hcounts.2 hYle
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  change jointSensitivityAt _ _ x ≤ _ at hh
  have hcharges := Nat.add_le_add hU hV
  exact hh.trans (hcharges.trans (by simpa only [Nat.add_assoc] using hnum))

end
end SensitivityOrdinaryGuard

namespace SensitivityNQ
noncomputable section
variable {n : ℕ}

def rawZeroOrdinary (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  if 3 ≤ i.val ∧ C.tol i = C.tol j then
    min (rawZeroCoupled k t v C Z Y i j)
      (SensitivityOrdinaryGuard.ordinaryCost (C.tol j) (v (C.tol j))
        (Z (C.target i) (C.target j)) (Z (C.gate j) (C.target j))
        (Y (C.gate j) (C.gate i)) (Y (C.gate j) (C.target j)))
  else rawZeroCoupled k t v C Z Y i j

theorem labeling_defect_zero {k t : ℕ} (T : Tournament k) (L : Labeling T 2 t) :
    DefectBound T L.label 0 t := by
  intro S m hm
  apply L.coherent_card S m
  intro i hi j hj hij
  by_contra hne
  have hzero : (S.filter fun j => T.Adj i j ∧ L.label i j ≠ m j).card = 0 := by
    have hh := hm i hi
    omega
  have hempty := Finset.card_eq_zero.mp hzero
  have hmem : j ∈ S.filter (fun j => T.Adj i j ∧ L.label i j ≠ m j) :=
    Finset.mem_filter.mpr ⟨hj, hij, hne⟩
  simp only [hempty, Finset.notMem_empty] at hmem

theorem stage_zero_ordinary {k t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T 2 t) (ht : 4 ≤ t)
    (v : ℕ → ℕ) (hv : v 0 = t) (C : Recipe n) (hC : C.Valid)
    (hDefect : ∀ j : Fin n, 3 ≤ j.val → 0 < C.tol j →
      DefectBound T L.label (C.tol j) (v (C.tol j)))
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (Z Y : Fin n → Fin n → ℕ) (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (hc : Compatible C Z Y) :
    PairBound (stage T L.label C F) false (rawZeroOrdinary k t v C Z Y) := by
  have hold := stage_zero_coupled T L ht v C hC hDefect F hF Z Y hZ hY hc
  intro i j hij x hx hx'
  unfold rawZeroOrdinary
  split_ifs with he
  · apply le_min (hold i j hij x hx hx')
    have hj : 3 ≤ j.val := by omega
    have hpair := hC.2.2 i j hij he.1
    have hcompat := hc i j hij he.1
    have hd : DefectBound T L.label (C.tol j) (v (C.tol j)) := by
      by_cases hq : C.tol j = 0
      · rw [hq, hv]
        exact labeling_defect_zero T L
      · exact hDefect j hj (by omega)
    have hi3 : ¬i.val < 3 := by omega
    have hj3 : ¬j.val < 3 := by omega
    simp only [stage, if_neg hi3, if_neg hj3] at hx hx' ⊢
    simpa only [he.2] using
      (SensitivityOrdinaryGuard.ordinary_pair_zero T L.label hd F hF (by decide)
        Z Y hZ hY (C.target i) (C.target j) (C.gate i) (C.gate j)
        (hC.1 hij) hpair.1 hpair.2.2 hcompat.1 hcompat.2 x
        (by simpa only [he.2] using hx) hx')
  · exact hold i j hij x hx hx'

theorem rawZeroOrdinary_mul (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (w : ℕ) (i j : Fin n) :
    rawZeroOrdinary k t v C (fun i j => Z i j*w) (fun i j => Y i j*w) i j =
      rawZeroOrdinary k t v C Z Y i j*w := by
  unfold rawZeroOrdinary
  split_ifs <;> simp only [rawZeroCoupled_mul,
    SensitivityOrdinaryGuard.ordinaryCost_mul, min_mul]

end
end SensitivityNQ
end



/- Component: Research.SourceStrictStage -/
section
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators
namespace SensitivitySourceZero
noncomputable section

theorem mixed_pair_zero_source_strict {n k r t w : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : Labeling T r t)
    (hSource : SourceBound T A.label w) (hw : 4 ≤ w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (ht : 4 ≤ t)
    (Z Y : Fin n → Fin n → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hGA : Gi ≤ Ai)
    (hZA : Z Gj Aj ≤ Z Ai Aj) (hYK : Y Gj Aj ≤ Y Gj Gi)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : mixedFamily T A.label F Ai Gi x = false)
    (hx' : mixedFamily T A.label F Aj Gj x = false) :
    jointSensitivityAt (mixedFamily T A.label F Ai Gi)
      (mixedFamily T A.label F Aj Gj) x ≤
      strictSourceCost t w (Z Ai Aj) (Z Gj Aj) (Y Gj Gi) (Y Gj Aj) := by
  let S := twoPred F Gj Aj
  have hS : NestedFamily S := twoPred_nested F hF Gj Aj (hG.trans (hGA.trans hA))
  let TC := targetCandidates T A.label S 0 x
  let GC := gateCandidates T A.label S 0 x
  let tw := targetWitness S x hr
  let gw := gateWitness T A.label S 0 x
  let T0 := TC.filter fun i => F Gj (recursiveChild x i (tw i)) = false
  let T1 := TC.filter fun i => F Gj (recursiveChild x i (tw i)) = true
  let G0 := GC.filter fun i => F Aj (recursiveChild x (gw i) (A.label i (gw i))) = false
  let G1 := GC.filter fun i => F Aj (recursiveChild x (gw i) (A.label i (gw i))) = true
  let U := T1.biUnion fun i => childJointChanges F Ai Aj x i (tw i)
  let V := T0.biUnion fun i => childJointChanges F Gj Aj x i (tw i)
  let W := G0.biUnion fun i => childJointChanges F Gj Gi x (gw i) (A.label i (gw i))
  let X := G1.biUnion fun i => childJointChanges F Gj Aj x (gw i) (A.label i (gw i))
  have hsub : (Finset.univ.filter fun p =>
      mixedFamily T A.label F Ai Gi (flip x {p}) ≠ mixedFamily T A.label F Ai Gi x ∧
      mixedFamily T A.label F Aj Gj (flip x {p}) ≠ mixedFamily T A.label F Aj Gj x) ⊆
      (U ∪ V) ∪ (W ∪ X) := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon' : mixedFamily T A.label F Aj Gj (flip x {((j,c),a)}) = true := by
      cases hy : mixedFamily T A.label F Aj Gj (flip x {((j,c),a)})
      · exact False.elim (hc.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T A.label S 0 _).mp hon'
    have hioff := (recursiveFamily_eq_false_iff T A.label S 0 x).mp hx' i
    rcases rowClause_repair_cases T A.label S 0 x i j c a hioff hi' with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      change F Aj (recursiveChild x i c) = false at htoff
      change F Aj (flip (recursiveChild x i c) {a}) = true at hton
      have hcw := targetWitness_unique T A.label S 0 x hr i hit c htoff
      have hweakoff : F Ai (recursiveChild x i c) = false := by
        rw [hcw]
        exact target_candidate_weak_false T A.label F hF Ai Aj Gi Gj hA hG x hr hx hit
      have hweakon := hF.accepts_of_le hA hton
      have hgon := hF.accepts_of_le (hG.trans (hGA.trans hA)) hton
      apply Finset.mem_union_left
      cases hz : F Gj (recursiveChild x i c)
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hz
        · have hn : F Gj (flip (recursiveChild x i c) {a}) ≠
                F Gj (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠
                F Aj (recursiveChild x i c) := by simp [hgon, hz, hton, htoff]
          simpa [childJointChanges, tw, hcw] using hn
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hz
        · have hn : F Ai (flip (recursiveChild x i c) {a}) ≠
                F Ai (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠
                F Aj (recursiveChild x i c) := by
            simp [hweakon, hweakoff, hton, htoff]
          simpa [childJointChanges, tw, hcw] using hn
    · change F Gj (recursiveChild x j (A.label i j)) = true at hgon
      change F Gj (flip (recursiveChild x j (A.label i j)) {a}) = false at hgoff
      have hjw := gateWitness_unique T A.label S 0 x i hig j hij hgon
      have hwgon := gate_candidate_weak_true T A.label F hF Ai Aj Gi Gj hA hG x hx hig
      have hweakon : F Gi (recursiveChild x j (A.label i j)) = true := by
        simpa [hjw] using hwgon
      have hweakoff := hF.rejects_of_le hG hgoff
      apply Finset.mem_union_right
      cases hto : F Aj (recursiveChild x j (A.label i j))
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hig, ?_⟩, ?_⟩
        · simpa only [gw, ← hjw] using hto
        · have hn : F Gj (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F Gj (recursiveChild x j (A.label i j)) ∧
              F Gi (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F Gi (recursiveChild x j (A.label i j)) := by
            simp [hgon, hgoff, hweakon, hweakoff]
          simpa [childJointChanges, gw, hjw] using hn
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hig, ?_⟩, ?_⟩
        · simpa only [gw, ← hjw] using hto
        · have htf := hF.rejects_of_le (hG.trans (hGA.trans hA)) hgoff
          have hn : F Gj (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F Gj (recursiveChild x j (A.label i j)) ∧
              F Aj (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F Aj (recursiveChild x j (A.label i j)) := by
            simp [hgon, hgoff, hto, htf]
          simpa [childJointChanges, gw, hjw] using hn
  have hU : U.card ≤ T1.card * Z Ai Aj := by
    apply card_biUnion_le_mul
    intro i hi
    rw [childJointChanges_card]
    exact hZ _ _ hA _
      (target_candidate_weak_false T A.label F hF Ai Aj Gi Gj hA hG x hr hx
        (Finset.mem_filter.mp hi).1)
      (targetWitness_false T A.label S 0 x hr i (Finset.mem_filter.mp hi).1)
  have hV : V.card ≤ T0.card * Z Gj Aj := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hi, hz⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hZ _ _ (hG.trans (hGA.trans hA)) _ hz (targetWitness_false T A.label S 0 x hr i hi)
  have hW : W.card ≤ G0.card * Y Gj Gi := by
    apply card_biUnion_le_mul
    intro i hi
    have hg := (Finset.mem_filter.mp hi).1
    rw [childJointChanges_card]
    exact hY _ _ hG _ (gateWitness_spec T A.label S 0 x i hg).2
      (gate_candidate_weak_true T A.label F hF Ai Aj Gi Gj hA hG x hx hg)
  have hX : X.card ≤ G1.card * Y Gj Aj := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hi, ht⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hY _ _ (hG.trans (hGA.trans hA)) _ (gateWitness_spec T A.label S 0 x i hi).2 ht
  have hcost : jointSensitivityAt (mixedFamily T A.label F Ai Gi) (mixedFamily T A.label F Aj Gj) x ≤
      T1.card * Z Ai Aj + T0.card * Z Gj Aj +
      G0.card * Y Gj Gi + G1.card * Y Gj Aj := by
    have hu := Finset.card_union_le U V
    have hw := Finset.card_union_le W X
    have hc := Finset.card_union_le (U ∪ V) (W ∪ X)
    have hs := Finset.card_le_card hsub
    change jointSensitivityAt _ _ x ≤ _ at hs
    omega
  have hnsum : T0.card + T1.card = TC.card := by
    simpa [T0, T1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := TC)
        (fun i => F Gj (recursiveChild x i (tw i)) = false))
  have hmsum : G0.card + G1.card = GC.card := by
    simpa [G0, G1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := GC)
        (fun i => F Aj (recursiveChild x (gw i) (A.label i (gw i))) = false))
  have hn1 : T1.card ≤ 1 := target_sources_card T A.label S hS 0 x hr
  have hm0 : G0.card ≤ 1 := gate_false_targets_card T A.label S hS 0 x
  have hm : G0.card + G1.card ≤ 3 := by
    rw [hmsum]
    exact gateCandidates_card T A.label S hS 0 x
  have hn : T0.card + T1.card ≤ t-1 := by
    have hc := Sensitivity205.targetCandidates_card T A S hS 0 x hr
    change TC.card < t at hc
    omega
  have hTCeq : tolerantTargets T A.label F Aj Gj 0 x = TC :=
    tolerantTargets_zero T A.label F Aj Gj x
  have hGCeq : tolerantGuards T A.label F Aj Gj 0 x = GC :=
    (gateCandidates_twoPred T A.label F Aj Gj x).symm
  have hPeq : positiveTargets T A.label F Aj Gj 0 x hr = T1 :=
    positiveTargets_twoPred T A.label F Aj Gj x hr
  have hGJA : Gj ≤ Aj := hG.trans (hGA.trans hA)
  have hsource : 0 < T1.card+G0.card+G1.card → T0.card+T1.card ≤ w-1 := by
    intro hpos
    have hactive : 0 < (positiveTargets T A.label F Aj Gj 0 x hr).card+
        (tolerantGuards T A.label F Aj Gj 0 x).card := by
      rw [hPeq, hGCeq]
      omega
    have hh := targets_card_source_active T A.label hSource F hF Aj Gj hGJA x hr hactive
    rw [hTCeq] at hh
    omega
  have hordinary : 0 < G0.card → T0.card+T1.card ≤ w-2 := by
    intro hpos
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
    obtain ⟨hb, hbo⟩ := Finset.mem_filter.mp hb
    have hbO := gate_false_ordinary T A.label F Aj Gj x b hb hbo
    have hOG : 0 < (SensitivityOrdinaryGuard.ordinaryGuards T A.label F Aj Gj 0 x).card :=
      Finset.card_pos.mpr ⟨b, hbO⟩
    have hh := targets_ordinary_card_source T A.label hSource F hF Aj Gj hGJA x hr (by omega)
    rw [hTCeq] at hh
    omega
  have hnzero : 2 ≤ G0.card + G1.card → T1.card = 0 := by
    intro hg
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hi, hon⟩ := Finset.mem_filter.mp hi
    have hz := gate_card_two_targets_zero T A.label S hS 0 x hr
      (by simpa [hmsum] using hg) hi
    change F Gj (recursiveChild x i (tw i)) = false at hz
    change F Gj (recursiveChild x i (tw i)) = true at hon
    simp only [hz, Bool.false_eq_true] at hon
  have htwo0 : G0.card+G1.card = 2 → G0.card = 0 → T0.card ≤ w-2 := by
    intro hg _
    have hGC : 2 ≤ (tolerantGuards T A.label F Aj Gj 0 x).card := by
      rw [hGCeq]
      omega
    have hc := targets_card_add_one_source_of_two_guards T A.label hSource
      F hF Aj Gj hGJA x hr hGC
    rw [hTCeq] at hc
    omega
  have htwo1 : G0.card+G1.card = 2 → G0.card = 1 → T0.card ≤ w-3 := by
    intro hg hzero
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < G0.card)
    obtain ⟨hb, hbo⟩ := Finset.mem_filter.mp hb
    have hbO := gate_false_ordinary T A.label F Aj Gj x b hb hbo
    have hGC : 2 ≤ (tolerantGuards T A.label F Aj Gj 0 x).card := by
      rw [hGCeq]
      omega
    have hc := targets_card_add_two_source_of_two_guards_ordinary T A.label hSource
      F hF Aj Gj hGJA x hr hGC ⟨b, hbO⟩
    rw [hTCeq] at hc
    omega
  have hthree : G0.card + G1.card = 3 → G0.card = 0 ∧ T0.card ≤ w-3 := by
    intro hg
    have hgc : GC.card = 3 := by omega
    constructor
    · apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hi, ho⟩ := Finset.mem_filter.mp hi
      have hs := gate_false_target_sink T A.label S hS 0 x hi ho
      have hc := gate_sink_card_le_two T A.label S hS 0 x hs
      change GC.card ≤ 2 at hc
      omega
    · have hGC : (tolerantGuards T A.label F Aj Gj 0 x).card = 3 := by
        rw [hGCeq]
        exact hgc
      have hc := targets_card_add_two_source_of_three_guards T A.label hSource
        F hF Aj Gj hGJA x hr hGC
      rw [hTCeq] at hc
      omega
  exact hcost.trans (strict_weighted_bound T0.card T1.card G0.card G1.card t w
    (Z Ai Aj) (Y Gj Gi) (Z Gj Aj) (Y Gj Aj)
    hw hZA hYK hn1 hm0 hm hn hsource hordinary hnzero htwo0 htwo1 hthree)

end
end SensitivitySourceZero
end



/- Component: Research.SourceGuardStage -/
section
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open SensitivityOrdinaryGuard
open scoped Classical BigOperators
namespace SensitivitySourceZero
noncomputable section

theorem source_pair_zero {n k r v w : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r) (hDefect : DefectBound T label 0 v) (hSource : SourceBound T label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (Z Y : Fin n → Fin n → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hGA : Gi ≤ Ai)
    (hZle : Z Gj Aj ≤ Z Ai Aj) (hYle : Y Gj Aj ≤ Y Gj Gi)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T label F Ai Gi 0 x = false)
    (hx' : tolerantFamily T label F Aj Gj 0 x = false) :
    jointSensitivityAt (tolerantFamily T label F Ai Gi 0)
      (tolerantFamily T label F Aj Gj 0) x ≤
      sourceCost v w (Z Ai Aj) (Z Gj Aj) (Y Gj Gi) (Y Gj Aj) := by
  let TC := tolerantTargets T label F Aj Gj 0 x
  let GC := tolerantGuards T label F Aj Gj 0 x
  let OG := ordinaryGuards T label F Aj Gj 0 x
  let L := ordinaryTotal T label F Aj Gj 0 x
  let P := positiveTargets T label F Aj Gj 0 x hr
  let tw := missingWitness F Aj x hr
  let B := failedGuards T label F Gj x
  let U := splitTargetChanges F Ai Aj Gj Gj x TC tw
  let V := GC.biUnion fun i => (B i).biUnion fun j =>
    if F Aj (recursiveChild x j (label i j)) = false
      then childJointChanges F Gj Gi x j (label i j)
      else childJointChanges F Gj Aj x j (label i j)
  have hGJA : Gj ≤ Aj := hG.trans (hGA.trans hA)
  have hweakguard : ∀ i ∈ GC, ∀ j ∈ B i,
      F Gi (recursiveChild x j (label i j)) = true := by
    intro i hi j hj
    have he := tolerant_guard_sets_eq T label F hF Ai Aj Gi Gj hA hG x 0 hx hi
    have hj' : j ∈ failedGuards T label F Gi x i := by rw [he]; exact hj
    exact ((mem_failedGuards T label F Gi x i j).mp hj').2
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T label F Ai Gi 0 (flip x {p}) ≠ tolerantFamily T label F Ai Gi 0 x ∧
      tolerantFamily T label F Aj Gj 0 (flip x {p}) ≠ tolerantFamily T label F Aj Gj 0 x) ⊆
      U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T label F Aj Gj 0 (flip x {((j,c),a)}) = true := by
      cases hy : tolerantFamily T label F Aj Gj 0 (flip x {((j,c),a)})
      · exact False.elim (hc.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi⟩ := (tolerantFamily_true T label F Aj Gj 0 _).mp hon
    have hoff := (tolerantFamily_false T label F Aj Gj 0 x).mp hx' i
    rcases tolerant_repair_cases T label F Aj Gj 0 x i j c a hoff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, hcl, hgon, hgoff⟩
    · subst j
      have hcw := missingWitness_unique F Aj x hr i (Finset.mem_filter.mp hit).2.1 c htoff
      have hwo : F Ai (recursiveChild x i c) = false := by
        rw [hcw]
        exact tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
          (le_refl 0) hr hx hit
      have hwn := hF.accepts_of_le hA hton
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
          F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
        simp [hwo, hwn, htoff, hton]
      by_cases hgo : F Gj (recursiveChild x i (tw i)) = true
      · rw [if_pos hgo]
        simpa [childJointChanges, tw, hcw] using hn
      · rw [if_neg hgo]
        apply Finset.mem_inter.mpr
        constructor
        · simpa [childJointChanges, tw, hcw] using hn
        · have hgoff : F Gj (recursiveChild x i c) = false := by
            simpa only [tw, ← hcw, Bool.not_eq_true] using hgo
          have hgn := hF.accepts_of_le hGJA hton
          have hn0 : F Gj (flip (recursiveChild x i c) {a}) ≠ F Gj (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
            simp [hgoff, hgn, htoff, hton]
          simpa [childJointChanges, tw, hcw] using hn0
    · subst c
      have hj : j ∈ B i := (mem_failedGuards T label F Gj x i j).mpr ⟨hij, hgon⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hig, Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩⟩
      by_cases hfalse : F Aj (recursiveChild x j (label i j)) = false
      · rw [if_pos hfalse]
        have hwo := hweakguard i hig j hj
        have hwf := hF.rejects_of_le hG hgoff
        have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gj (recursiveChild x j (label i j)) ∧
            F Gi (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gi (recursiveChild x j (label i j)) := by simp [hgon, hgoff, hwo, hwf]
        simpa [childJointChanges] using hn
      · rw [if_neg hfalse]
        have hto : F Aj (recursiveChild x j (label i j)) = true := by
          cases hh : F Aj (recursiveChild x j (label i j)) <;> simp_all
        have htf := hF.rejects_of_le hGJA hgoff
        have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gj (recursiveChild x j (label i j)) ∧
            F Aj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Aj (recursiveChild x j (label i j)) := by simp [hgon, hgoff, hto, htf]
        simpa [childJointChanges] using hn
  let tv := effectiveCutoff v w P.card OG.card
  have hTU : TC.card+OG.card < tv := by
    by_cases hz : P.card+OG.card = 0
    · simpa only [tv, effectiveCutoff, if_pos hz] using
        (targets_ordinary_card T label hDefect F hF Aj Gj hGJA x hr)
    · simpa only [tv, effectiveCutoff, if_neg hz] using
        (targets_ordinary_card_source T label hSource F hF Aj Gj hGJA x hr
          (by change 0 < P.card+OG.card; omega))
  have hTC : TC.card ≤ tv-1-OG.card := by omega
  have hP : P.card ≤ TC.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hU : U.card ≤ P.card*Z Ai Aj+(tv-1-OG.card-P.card)*Z Gj Aj := by
    have hh := splitTargetChanges_card_count F Ai Aj Gj Gj hA hGJA Z hZ x TC tw
      (fun i hi => tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
        (le_refl 0) hr hx hi)
      (fun i hi => missingWitness_false F Aj x hr i (Finset.mem_filter.mp hi).2.1)
      (fun i hi hn => Bool.eq_false_iff.mpr hn)
    have hU0 : U.card ≤ P.card*Z Ai Aj+(TC.card-P.card)*Z Gj Aj := by
      simpa only [U, P, positiveTargets, TC, tw, min_eq_right hZle] using hh
    exact hU0.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hTC P.card)) _)
  have hV : V.card ≤ L*Y Gj Gi+(GC.card*(0+1)-L)*Y Gj Aj := by
    apply le_trans Finset.card_biUnion_le
    apply le_trans (Finset.sum_le_sum (fun i hi => Finset.card_biUnion_le))
    apply le_trans (Finset.sum_le_sum ?_)
      (ordinary_weight_identity T label F Aj Gj 0 x (Y Gj Gi) (Y Gj Aj)).le
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hgo := ((mem_failedGuards T label F Gj x i j).mp hj).2
    by_cases hfalse : F Aj (recursiveChild x j (label i j)) = false
    · rw [if_pos hfalse, if_pos hfalse, childJointChanges_card]
      exact hY _ _ hG _ hgo (hweakguard i hi j hj)
    · rw [if_neg hfalse, if_neg hfalse, childJointChanges_card]
      have hto : F Aj (recursiveChild x j (label i j)) = true := by
        cases hh : F Aj (recursiveChild x j (label i j)) <;> simp_all
      exact hY _ _ hGJA _ hgo hto
  have hcounts := ordinary_counts T label F hF Aj Gj hGJA 0 x
  change OG.card ≤ L ∧ L ≤ ordinaryLimit 0 GC.card OG.card at hcounts
  have hn : P.card ≤ 1 := by
    simpa only [Nat.mul_zero, zero_add] using
      (positiveTargets_card T label F hF Aj Gj hGJA 0 x hr)
  have hm : GC.card ≤ 3 := by
    simpa only [Nat.mul_zero, zero_add] using
      (guards_card T label F hF Aj Gj hGJA 0 x)
  have hc : (P.card+GC.card).choose 2 ≤ GC.card := by
    simpa only [Nat.zero_mul, zero_add, Nat.one_mul] using
      (positiveTargets_guards_coupling T label F hF Aj Gj hGJA 0 x hr)
  have hnum := charge_le_sourceCost v w (Z Ai Aj) (Z Gj Aj) (Y Gj Gi) (Y Gj Aj)
    P.card GC.card OG.card L hn hm
    (Finset.card_le_card (ordinaryGuards_subset T label F Aj Gj 0 x)) hc
    (by change P.card+OG.card ≤ tv-1; omega) hcounts.1 hcounts.2 hYle
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  change jointSensitivityAt _ _ x ≤ _ at hh
  have hcharges := Nat.add_le_add hU hV
  exact hh.trans (hcharges.trans (by simpa only [Nat.add_assoc, zero_add, Nat.mul_one] using hnum))


end
end SensitivitySourceZero

namespace SensitivityNQ
noncomputable section
variable {n : ℕ}

def rawZeroSource (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  if 3 ≤ i.val ∧ C.tol i = 0 ∧ C.tol j = 0 then
    min (rawZeroOrdinary k t v C Z Y i j)
      (SensitivitySourceZero.sourceCost t w
        (Z (C.target i) (C.target j)) (Z (C.gate j) (C.target j))
        (Y (C.gate j) (C.gate i)) (Y (C.gate j) (C.target j)))
  else rawZeroOrdinary k t v C Z Y i j

theorem stage_zero_source {k t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T 2 t) (ht : 4 ≤ t)
    (v : ℕ → ℕ) (hv : v 0 = t) (w : ℕ)
    (hSource : SensitivitySourceZero.SourceBound T L.label w)
    (C : Recipe n) (hC : C.Valid)
    (hDefect : ∀ j : Fin n, 3 ≤ j.val → 0 < C.tol j →
      DefectBound T L.label (C.tol j) (v (C.tol j)))
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (Z Y : Fin n → Fin n → ℕ) (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (hc : Compatible C Z Y) :
    PairBound (stage T L.label C F) false (rawZeroSource k t v w C Z Y) := by
  have hold := stage_zero_ordinary T L ht v hv C hC hDefect F hF Z Y hZ hY hc
  intro i j hij x hx hx'
  unfold rawZeroSource
  split_ifs with he
  · apply le_min (hold i j hij x hx hx')
    have hj : 3 ≤ j.val := by omega
    have hpair := hC.2.2 i j hij he.1
    have hcompat := hc i j hij he.1
    have hi3 : ¬i.val < 3 := by omega
    have hj3 : ¬j.val < 3 := by omega
    simp only [stage, if_neg hi3, if_neg hj3] at hx hx' ⊢
    simp only [he.2.1, he.2.2] at hx hx' ⊢
    exact SensitivitySourceZero.source_pair_zero T L.label (labeling_defect_zero T L)
      hSource F hF (by decide) Z Y hZ hY
      (C.target i) (C.target j) (C.gate i) (C.gate j)
      (hC.1 hij) hpair.1 hpair.2.2 hcompat.1 hcompat.2 x hx hx'
  · exact hold i j hij x hx hx'

theorem rawZeroSource_mul (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (s : ℕ) (i j : Fin n) :
    rawZeroSource k t v w C (fun i j => Z i j*s) (fun i j => Y i j*s) i j =
      rawZeroSource k t v w C Z Y i j*s := by
  unfold rawZeroSource
  split_ifs <;> simp only [rawZeroOrdinary_mul,
    SensitivitySourceZero.sourceCost_mul, min_mul]

end
end SensitivityNQ
end



/- Component: Research.SourceTargetStage -/
section
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators
namespace SensitivitySourceZero
noncomputable section

theorem strict_ordinary_pair_zero_source {n k r t w : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T r t)
    (hSource : SourceBound T L.label w)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (Z : Fin n → Fin n → ℕ) (hZ : PairBound F false Z)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hGA : Gi ≤ Ai)
    (q : ℕ) (hq : 0 < q)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T L.label F Ai Gi q x = false)
    (hx' : tolerantFamily T L.label F Aj Gj 0 x = false) :
    jointSensitivityAt (tolerantFamily T L.label F Ai Gi q)
      (tolerantFamily T L.label F Aj Gj 0) x ≤
      max (Z Ai Aj+(w-2)*Z Gj Aj) ((t-1)*Z Gj Aj) := by
  let S := twoPred F Gj Aj
  let TC := tolerantTargets T L.label F Aj Gj 0 x
  let tw := missingWitness F Aj x hr
  let T0 := TC.filter fun i => F Gj (recursiveChild x i (tw i)) = false
  let T1 := TC.filter fun i => F Gj (recursiveChild x i (tw i)) = true
  let U := T1.biUnion fun i => childJointChanges F Ai Aj x i (tw i)
  let V := T0.biUnion fun i => childJointChanges F Gj Aj x i (tw i)
  have hGJA : Gj ≤ Aj := hG.trans (hGA.trans hA)
  have hS : NestedFamily S := twoPred_nested F hF Gj Aj hGJA
  have htw : ∀ i, tw i = targetWitness S x hr i := by intro i; rfl
  have hTC : TC = targetCandidates T L.label S 0 x := tolerantTargets_zero T L.label F Aj Gj x
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T L.label F Ai Gi q (flip x {p}) ≠ tolerantFamily T L.label F Ai Gi q x ∧
      tolerantFamily T L.label F Aj Gj 0 (flip x {p}) ≠ tolerantFamily T L.label F Aj Gj 0 x) ⊆
      U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T L.label F Aj Gj 0 (flip x {((j,c),a)}) = true := by
      cases hy : tolerantFamily T L.label F Aj Gj 0 (flip x {((j,c),a)})
      · exact False.elim (hc.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi⟩ := (tolerantFamily_true T L.label F Aj Gj 0 _).mp hon
    have hoff := (tolerantFamily_false T L.label F Aj Gj 0 x).mp hx' i
    rcases tolerant_repair_cases T L.label F Aj Gj 0 x i j c a hoff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, _⟩
    · subst j
      have hcw := missingWitness_unique F Aj x hr i (Finset.mem_filter.mp hit).2.1 c htoff
      have hwo : F Ai (recursiveChild x i c) = false := by
        rw [hcw]
        exact tolerant_target_weak_false T L.label F hF Ai Aj Gi Gj hA hG x
          (Nat.zero_le q) hr hx hit
      have hwn := hF.accepts_of_le hA hton
      have hgn := hF.accepts_of_le hGJA hton
      cases hgo : F Gj (recursiveChild x i c)
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hgo
        · have hn : F Gj (flip (recursiveChild x i c) {a}) ≠ F Gj (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
            simp [hgo, hgn, htoff, hton]
          simpa [childJointChanges, tw, hcw] using hn
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hgo
        · have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
            simp [hwo, hwn, htoff, hton]
          simpa [childJointChanges, tw, hcw] using hn
    · exact False.elim (no_guard_candidate_of_strict T L.label F hF Ai Aj Gi Gj hA hG x hq hx hig)
  have hU : U.card ≤ T1.card*Z Ai Aj := by
    apply card_biUnion_le_mul
    intro i hi
    have hit := (Finset.mem_filter.mp hi).1
    rw [childJointChanges_card]
    exact hZ _ _ hA _
      (tolerant_target_weak_false T L.label F hF Ai Aj Gi Gj hA hG x (Nat.zero_le q) hr hx hit)
      (missingWitness_false F Aj x hr i (Finset.mem_filter.mp hit).2.1)
  have hV : V.card ≤ T0.card*Z Gj Aj := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hit, hgo⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hZ _ _ hGJA _ hgo (missingWitness_false F Aj x hr i (Finset.mem_filter.mp hit).2.1)
  have hnsum : T0.card+T1.card = TC.card := by
    simpa [T0, T1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := TC)
        (fun i => F Gj (recursiveChild x i (tw i)) = false))
  have hn1 : T1.card ≤ 1 := by
    have hh := target_sources_card T L.label S hS 0 x hr
    change ((targetCandidates T L.label S 0 x).filter fun i =>
      F Gj (recursiveChild x i (targetWitness S x hr i)) = true).card ≤ 1 at hh
    simpa only [T1, hTC, htw] using hh
  have hn : T0.card+T1.card ≤ t-1 := by
    have hh := Sensitivity205.targetCandidates_card T L S hS 0 x hr
    rw [← hTC] at hh
    omega
  have hsource : 0 < T1.card → T0.card+T1.card ≤ w-1 := by
    intro hpos
    have hh := targets_ordinary_card_source T L.label hSource F hF Aj Gj hGJA x hr
      (by change 0 < T1.card+(SensitivityOrdinaryGuard.ordinaryGuards T L.label F Aj Gj 0 x).card; omega)
    change TC.card+(SensitivityOrdinaryGuard.ordinaryGuards T L.label F Aj Gj 0 x).card < w at hh
    omega
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  change jointSensitivityAt _ _ x ≤ _ at hh
  exact (hh.trans (Nat.add_le_add hU hV)).trans
    (target_source_arithmetic T0.card T1.card t w (Z Ai Aj) (Z Gj Aj) hn1 hn hsource)


theorem aux_ordinary_zero_source {n k t w : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T 2 t)
    (hSource : SourceBound T L.label w) (s : Fin 3)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A B G : Fin n) (hAB : A ≤ B) (hGB : G ≤ B)
    (Z : Fin n → Fin n → ℕ) (hZ : PairBound F false Z)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : auxFamily s F A x = false)
    (hx' : tolerantFamily T L.label F B G 0 x = false) :
    jointSensitivityAt (auxFamily s F A) (tolerantFamily T L.label F B G 0) x ≤
      max (Z A B+(w-2)*Z (min A G) B) ((t-1)*Z (min A G) B) := by
  let S := twoPred F G B
  let TC := tolerantTargets T L.label F B G 0 x
  let tw := missingWitness F B x (by decide)
  let T0 := TC.filter fun i => F G (recursiveChild x i (tw i)) = false
  let T1 := TC.filter fun i => F G (recursiveChild x i (tw i)) = true
  let U := T1.biUnion fun i => childJointChanges F A B x i (tw i)
  let V := T0.biUnion fun i => childJointChanges F (min A G) B x i (tw i)
  have hGJA : G ≤ B := hGB
  have hS : NestedFamily S := twoPred_nested F hF G B hGJA
  have htw : ∀ i, tw i = targetWitness S x (by decide) i := by intro i; rfl
  have hTC : TC = targetCandidates T L.label S 0 x := tolerantTargets_zero T L.label F B G x
  have hlow (i : Fin k) (hi : i ∈ T0) : F (min A G) (recursiveChild x i (tw i)) = false := by
    obtain ⟨hit, hgo⟩ := Finset.mem_filter.mp hi
    have hao := aux_target_false s F hF A B hAB x hx i (Finset.mem_filter.mp hit).2.1
    rcases le_total A G with hag | hga
    · simpa only [min_eq_left hag] using hao
    · simpa only [min_eq_right hga] using hgo
  have hminB : min A G ≤ B := (min_le_left _ _).trans hAB
  have hsub : jointChanges (auxFamily s F A) (tolerantFamily T L.label F B G 0) x ⊆ U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T L.label F B G 0 (flip x {((j,c),a)}) = true := by
      simpa only [hx', Bool.not_eq_false] using hc.2
    obtain ⟨hit, he, hao, hbo, hbn⟩ := aux_target_repair T L.label s F hF A B G hAB 0 x hx hx' j c a hon
    have han := hF.accepts_of_le hAB hbn
    cases hgo : F G (recursiveChild x j c)
    · have ht0 : j ∈ T0 := Finset.mem_filter.mpr ⟨hit, by simpa only [tw, ← he] using hgo⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j, ht0, ?_⟩
      have hlo : F (min A G) (recursiveChild x j c) = false := by simpa only [tw, ← he] using hlow j ht0
      have hln := hF.accepts_of_le hminB hbn
      have hn : F (min A G) (flip (recursiveChild x j c) {a}) ≠ F (min A G) (recursiveChild x j c) ∧
          F B (flip (recursiveChild x j c) {a}) ≠ F B (recursiveChild x j c) := by simp [hlo,hln,hbo,hbn]
      simpa [childJointChanges,tw,he] using hn
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨hit, by simpa only [tw, ← he] using hgo⟩, ?_⟩
      have hn : F A (flip (recursiveChild x j c) {a}) ≠ F A (recursiveChild x j c) ∧
          F B (flip (recursiveChild x j c) {a}) ≠ F B (recursiveChild x j c) := by simp [hao,han,hbo,hbn]
      simpa [childJointChanges,tw,he] using hn
  have hU : U.card ≤ T1.card*Z A B := by
    apply card_biUnion_le_mul
    intro i hi
    have hit := (Finset.mem_filter.mp hi).1
    rw [childJointChanges_card]
    exact hZ _ _ hAB _
      (aux_target_false s F hF A B hAB x hx i (Finset.mem_filter.mp hit).2.1)
      (missingWitness_false F B x (by decide) i (Finset.mem_filter.mp hit).2.1)
  have hV : V.card ≤ T0.card*Z (min A G) B := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hit, hgo⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hZ _ _ hminB _ (hlow i hi) (missingWitness_false F B x (by decide) i (Finset.mem_filter.mp hit).2.1)
  have hnsum : T0.card+T1.card = TC.card := by
    simpa [T0, T1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := TC)
        (fun i => F G (recursiveChild x i (tw i)) = false))
  have hn1 : T1.card ≤ 1 := by
    have hh := target_sources_card T L.label S hS 0 x (by decide)
    change ((targetCandidates T L.label S 0 x).filter fun i =>
      F G (recursiveChild x i (targetWitness S x (by decide) i)) = true).card ≤ 1 at hh
    simpa only [T1, hTC, htw] using hh
  have hn : T0.card+T1.card ≤ t-1 := by
    have hh := Sensitivity205.targetCandidates_card T L S hS 0 x (by decide)
    rw [← hTC] at hh
    omega
  have hsource : 0 < T1.card → T0.card+T1.card ≤ w-1 := by
    intro hpos
    have hh := targets_ordinary_card_source T L.label hSource F hF B G hGJA x (by decide)
      (by change 0 < T1.card+(SensitivityOrdinaryGuard.ordinaryGuards T L.label F B G 0 x).card; omega)
    change TC.card+(SensitivityOrdinaryGuard.ordinaryGuards T L.label F B G 0 x).card < w at hh
    omega
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  change jointSensitivityAt _ _ x ≤ _ at hh
  exact (hh.trans (Nat.add_le_add hU hV)).trans
    (target_source_arithmetic T0.card T1.card t w (Z A B) (Z (min A G) B) hn1 hn hsource)


end
end SensitivitySourceZero
end



/- Component: Research.SourceFullStage -/
section
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators
namespace SensitivityNQ
noncomputable section
variable {n : ℕ}

def rawZeroSourceFull (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  let a := Z (C.target i) (C.target j)
  let b := Z (C.gate j) (C.target j)
  let c := Y (C.gate j) (C.gate i)
  let e := Y (C.gate j) (C.target j)
  if j.val < 3 then rawZeroSource k t v w C Z Y i j
  else if i.val < 3 then
    if C.aux i = 0 then rawZeroSource k t v w C Z Y i j
    else if C.tol j = 0 then
      max (a+(w-2)*Z (min (C.target i) (C.gate j)) (C.target j))
        ((t-1)*Z (min (C.target i) (C.gate j)) (C.target j))
    else rawZeroSource k t v w C Z Y i j
  else if C.tol j = 0 then
    if C.tol i = 0 then
      min (rawZeroSource k t v w C Z Y i j)
        (SensitivitySourceZero.strictSourceCost t w a b c e)
    else max (a+(w-2)*b) ((t-1)*b)
  else rawZeroSource k t v w C Z Y i j

theorem stage_zero_source_full {k t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T 2 t) (ht : 4 ≤ t)
    (v : ℕ → ℕ) (hv : v 0 = t) (w : ℕ) (hw : 4 ≤ w)
    (hSource : SensitivitySourceZero.SourceBound T L.label w)
    (C : Recipe n) (hC : C.Valid)
    (hDefect : ∀ j : Fin n, 3 ≤ j.val → 0 < C.tol j →
      DefectBound T L.label (C.tol j) (v (C.tol j)))
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (Z Y : Fin n → Fin n → ℕ) (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (hc : Compatible C Z Y) :
    PairBound (stage T L.label C F) false (rawZeroSourceFull k t v w C Z Y) := by
  have hold := stage_zero_source T L ht v hv w hSource C hC hDefect F hF Z Y hZ hY hc
  intro i j hij x hx hx'
  have hA := hC.1 hij
  unfold rawZeroSourceFull
  by_cases hj : j.val < 3
  · rw [if_pos hj]
    exact hold i j hij x hx hx'
  · rw [if_neg hj]
    have hGB := (hC.2.2 j j le_rfl (by omega)).2.2
    by_cases hi : i.val < 3
    · rw [if_pos hi]
      by_cases hu : C.aux i = 0
      · rw [if_pos hu]
        exact hold i j hij x hx hx'
      · rw [if_neg hu]
        by_cases hq : C.tol j = 0
        · rw [if_pos hq]
          simp only [stage, if_pos hi, if_neg hj] at hx hx' ⊢
          simp only [hq] at hx' ⊢
          exact SensitivitySourceZero.aux_ordinary_zero_source T L hSource
            (C.aux i) F hF (C.target i) (C.target j) (C.gate j) hA hGB Z hZ x hx hx'
        · rw [if_neg hq]
          exact hold i j hij x hx hx'
    · rw [if_neg hi]
      have hh := hC.2.2 i j hij (by omega)
      have hb := hc i j hij (by omega)
      by_cases hqj : C.tol j = 0
      · rw [if_pos hqj]
        by_cases hqi : C.tol i = 0
        · rw [if_pos hqi]
          apply le_min (hold i j hij x hx hx')
          simp only [stage, if_neg hi, if_neg hj, hqi, hqj, tolerant_zero_eq_mixed] at hx hx' ⊢
          exact SensitivitySourceZero.mixed_pair_zero_source_strict T L hSource hw
            F hF (by decide) ht Z Y hZ hY (C.target i) (C.target j) (C.gate i) (C.gate j)
            hA hh.1 hh.2.2 hb.1 hb.2 x hx hx'
        · rw [if_neg hqi]
          simp only [stage, if_neg hi, if_neg hj, hqj] at hx hx' ⊢
          exact SensitivitySourceZero.strict_ordinary_pair_zero_source T L hSource F hF
            (by decide) Z hZ (C.target i) (C.target j) (C.gate i) (C.gate j)
            hA hh.1 hh.2.2 (C.tol i) (by omega) x hx hx'
      · rw [if_neg hqj]
        exact hold i j hij x hx hx'

theorem rawZeroSourceFull_mul (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (s : ℕ) (i j : Fin n) :
    rawZeroSourceFull k t v w C (fun i j => Z i j*s) (fun i j => Y i j*s) i j =
      rawZeroSourceFull k t v w C Z Y i j*s := by
  unfold rawZeroSourceFull
  split_ifs <;> simp only [rawZeroSource_mul, SensitivitySourceZero.strictSourceCost_mul,
    Nat.add_mul, Nat.mul_assoc, max_mul, min_mul]

end
end SensitivityNQ
end



/- Component: Research.OrdinaryGuardPositiveArithmetic -/
section
/-! The ordinary guard charge after grouping arcs with the same positive
target head.  The internal nonordinary cap is a parameter so the ordinary
head argument can be combined with either the old arc count or the new
head-child bound. -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open scoped Classical

namespace SensitivityOrdinaryGuard
noncomputable section

def externalSlots (q m : ℕ) : ℕ := m*(q+1)-m.choose 2

/-- Residual outgoing budget after all arcs in the positive-target/guard
union are counted.  Under the coupled constraint this equals
`externalSlots - max(0,n*m+choose(n,2)-q*n)`. -/
def positiveResidual (q n m : ℕ) : ℕ :=
  min (externalSlots q m) (q*n+(q+1)*m-(n+m).choose 2)

def dedupLimit (q n m u : ℕ) : ℕ :=
  min (ordinaryLimit q m u) (positiveResidual q n m+u*n)

def dedupChoice (q n m u : ℕ) : ℕ :=
  max u (min (dedupLimit q n m u) (positiveResidual q n m+n))

def dedupCost (internal : ℕ → ℕ) (q v a b c e : ℕ) : ℕ :=
  (Finset.range (2*q+2)).sup fun n =>
    (Finset.range (2*q+4)).sup fun m =>
      (Finset.range (2*q+4)).sup fun u =>
        if (n+m).choose 2 ≤ q*n+(q+1)*m ∧
            n+u ≤ v-1 ∧ u ≤ m ∧ u ≤ dedupLimit q n m u then
          n*a+(v-1-u-n)*b+
            min (dedupChoice q n m u) (positiveResidual q n m+n)*c+
            (externalSlots q m-dedupChoice q n m u+internal m)*e
        else 0




def ordinaryDedupInternalCost (r q v a b c e : ℕ) : ℕ :=
  dedupCost (fun m => min (m.choose 2) (r*m)) q v a b c e

theorem dedupLimit_le_external (q n m u : ℕ) :
    dedupLimit q n m u ≤ externalSlots q m :=
  (min_le_left _ _).trans (min_le_right _ _)

/-- A piecewise linear charge increases up to its ordinary cap and
decreases beyond it.  Its maximum on `[u,U]` is the clamped cap. -/
theorem clamp_charge (N u U C L c e : ℕ)
    (huL : u ≤ L) (hLU : L ≤ U) (hUN : U ≤ N) (hec : e ≤ c) :
    min L C*c+(N-L)*e ≤
      min (max u (min U C)) C*c+(N-max u (min U C))*e := by
  let Lstar := max u (min U C)
  have huU : u ≤ U := huL.trans hLU
  have hstarU : Lstar ≤ U := max_le huU (min_le_left _ _)
  by_cases hLC : L ≤ C
  · have hmin : L ≤ min U C := le_min hLU hLC
    have hLstar : L ≤ Lstar := hmin.trans (le_max_right _ _)
    have huC : u ≤ C := huL.trans hLC
    have hstarC : Lstar ≤ C := max_le huC (min_le_right _ _)
    simpa only [min_eq_left hLC, min_eq_left hstarC, Lstar] using
      (split_charge_mono N L Lstar c e hLstar (hstarU.trans hUN) hec)
  · have hCL : C ≤ L := by omega
    have hCU : C ≤ U := hCL.trans hLU
    have hstar : Lstar = max u C := by
      simp only [Lstar, min_eq_right hCU]
    have hCstar : C ≤ Lstar := by rw [hstar]; exact le_max_right _ _
    have hstarL : Lstar ≤ L := by rw [hstar]; exact max_le huL hCL
    have htail : (N-L)*e ≤ (N-Lstar)*e :=
      Nat.mul_le_mul_right e (Nat.sub_le_sub_left hstarL N)
    simpa only [min_eq_right hCL, min_eq_right hCstar, Lstar] using
      Nat.add_le_add_left htail (C*c)

theorem charge_le_dedupCost (internal : ℕ → ℕ)
    (q v a b c e n m u L : ℕ)
    (hn : n ≤ 2*q+1) (hm : m ≤ 2*q+3) (hu : u ≤ m)
    (hc : (n+m).choose 2 ≤ q*n+(q+1)*m)
    (hnu : n+u ≤ v-1) (huL : u ≤ L)
    (hL : L ≤ dedupLimit q n m u) (hec : e ≤ c) :
    n*a+(v-1-u-n)*b+min L (positiveResidual q n m+n)*c+
      (externalSlots q m-L+internal m)*e ≤
      dedupCost internal q v a b c e := by
  let M := externalSlots q m
  let U := dedupLimit q n m u
  let C := positiveResidual q n m+n
  have hUM : U ≤ M := dedupLimit_le_external q n m u
  have hLM : L ≤ M := hL.trans hUM
  have hstarM : dedupChoice q n m u ≤ M :=
    max_le ((huL.trans hL).trans hUM) ((min_le_left _ _).trans hUM)
  have hNU : U ≤ M+internal m := hUM.trans (Nat.le_add_right _ _)
  have hcharge := clamp_charge (M+internal m) u U C L c e huL hL hNU hec
  have hsubL : M+internal m-L = M-L+internal m := by omega
  have hsubS : M+internal m-dedupChoice q n m u =
      M-dedupChoice q n m u+internal m := by omega
  change min L C*c+(M+internal m-L)*e ≤
    min (dedupChoice q n m u) C*c+
      (M+internal m-dedupChoice q n m u)*e at hcharge
  rw [hsubL, hsubS] at hcharge
  have htotal : n*a+(v-1-u-n)*b+min L C*c+(M-L+internal m)*e ≤
      n*a+(v-1-u-n)*b+min (dedupChoice q n m u) C*c+
        (M-dedupChoice q n m u+internal m)*e := by
    simpa only [Nat.add_assoc] using
      Nat.add_le_add_left hcharge (n*a+(v-1-u-n)*b)
  apply htotal.trans
  unfold dedupCost
  apply Finset.le_sup_of_le (b := n) (Finset.mem_range.mpr (by omega))
  apply Finset.le_sup_of_le (b := m) (Finset.mem_range.mpr (by omega))
  apply Finset.le_sup_of_le (b := u) (Finset.mem_range.mpr (by omega))
  rw [if_pos ⟨hc, hnu, hu, huL.trans hL⟩]

theorem dedupCost_mul (internal : ℕ → ℕ) (q v a b c e w : ℕ) :
    dedupCost internal q v (a*w) (b*w) (c*w) (e*w) =
      dedupCost internal q v a b c e*w := by
  unfold dedupCost
  rw [Finset.sup_mul₀]
  congr 1
  funext n
  rw [Finset.sup_mul₀]
  congr 1
  funext m
  rw [Finset.sup_mul₀]
  congr 1
  funext u
  split_ifs <;> simp only [Nat.zero_mul, Nat.add_mul, Nat.mul_assoc]

end
end SensitivityOrdinaryGuard
end



/- Component: Research.UsedGuardHeads -/
section
/-! A one-color-per-used-head coordinate union.  A cardinal bound is needed
only at a head receiving an actual selected arc, not at every member of P. -/

set_option autoImplicit false

open scoped Classical BigOperators

namespace SensitivitySharedGuardHead
noncomputable section

/-- If every selected arc into P uses that head's fixed color, its union
costs at most one derivative set per head.  Both the color equality and the
cardinal bound are supplied by an actual incoming arc witness. -/
theorem used_head_union_card {S H C α : Type}
    [DecidableEq S] [DecidableEq H] [DecidableEq α]
    (R : Finset S) (B : S → Finset H) (P : Finset H)
    (label : S → H → C) (color : H → C) (D : H → C → Finset α) (e : ℕ)
    (hlabel : ∀ i ∈ R, ∀ j ∈ B i, j ∈ P → label i j = color j)
    (hcard : ∀ i ∈ R, ∀ j ∈ B i, j ∈ P → (D j (label i j)).card ≤ e) :
    (R.biUnion fun i => ((B i).filter fun j => j ∈ P).biUnion fun j =>
      D j (label i j)).card ≤ P.card*e := by
  classical
  let used := P.filter fun j => ∃ i ∈ R, j ∈ B i
  let V := R.biUnion fun i => ((B i).filter fun j => j ∈ P).biUnion fun j =>
    D j (label i j)
  let U := used.biUnion fun j => D j (color j)
  have hVU : V ⊆ U := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hjB, hjP⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨hjP, ⟨i, hi, hjB⟩⟩, ?_⟩
    simpa only [hlabel i hi j hjB hjP] using hp
  have hD (j : H) (hj : j ∈ used) : (D j (color j)).card ≤ e := by
    obtain ⟨hjP, i, hi, hjB⟩ := Finset.mem_filter.mp hj
    have hh := hcard i hi j hjB hjP
    simpa only [hlabel i hi j hjB hjP] using hh
  have hU : U.card ≤ used.card*e := by
    calc
      U.card ≤ ∑ j ∈ used, (D j (color j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ used, e := Finset.sum_le_sum hD
      _ = used.card*e := by simp
  change V.card ≤ _
  exact (Finset.card_le_card hVU).trans (hU.trans
    (Nat.mul_le_mul_right e (Finset.card_le_card (Finset.filter_subset _ _))))

end
end SensitivitySharedGuardHead
end



/- Component: Research.OrdinaryGuardPositiveGeometry -/
section
/-! Ordinary failed arcs landing at a positive target head all select
that head's unique missing target child.  The remaining ordinary arcs
consume the residual outgoing budget of the positive-target/guard union. -/

set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators

namespace SensitivityOrdinaryGuard
noncomputable section

/-- A finite tournament budget with additional arcs outside the complete
positive-source union.  No Boolean predicates or labels occur here. -/
theorem tournament_outside_budget {k : ℕ} (T : Tournament k)
    (P R : Finset (Fin k)) (B O : Fin k → Finset (Fin k)) (q : ℕ)
    (hdis : Disjoint P R)
    (hinside : ∀ i, (P ∪ R).filter (T.Adj i) ⊆ B i)
    (hP : ∀ i ∈ P, (B i).card ≤ q)
    (hR : ∀ i ∈ R, (B i).card = q+1)
    (hOB : ∀ i, O i ⊆ B i)
    (hOR : ∀ i, ∀ j ∈ O i, j ∉ R) :
    (∑ i ∈ R, ((O i).filter fun j => j ∉ P).card)+
      (P.card+R.card).choose 2 ≤ q*P.card+(q+1)*R.card := by
  let S := P ∪ R
  let W := ∑ i ∈ R, ((O i).filter fun j => j ∉ P).card
  have hlocalP : ∀ i ∈ P, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    exact (Finset.card_le_card (hinside i)).trans (hP i hi)
  have hlocalR : ∀ i ∈ R,
      ((O i).filter fun j => j ∉ P).card+
        (S.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have hd : Disjoint ((O i).filter fun j => j ∉ P) (S.filter (T.Adj i)) := by
      apply Finset.disjoint_left.mpr
      intro j hjO hjS
      obtain ⟨hjO, hjnotP⟩ := Finset.mem_filter.mp hjO
      obtain ⟨hjS, _⟩ := Finset.mem_filter.mp hjS
      rcases Finset.mem_union.mp hjS with hjP | hjR
      · exact hjnotP hjP
      · exact hOR i j hjO hjR
    calc
      _ = (((O i).filter fun j => j ∉ P) ∪ S.filter (T.Adj i)).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ (B i).card := Finset.card_le_card (Finset.union_subset
        ((Finset.filter_subset _ _).trans (hOB i)) (hinside i))
      _ = q+1 := hR i hi
  have hs : (P.card+R.card).choose 2 =
      (∑ i ∈ P, (S.filter (T.Adj i)).card)+
        ∑ i ∈ R, (S.filter (T.Adj i)).card := by
    calc
      _ = S.card.choose 2 := by
        rw [show S.card = P.card+R.card from Finset.card_union_of_disjoint hdis]
      _ = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
        rw [T.sum_outdegree_eq, T.card_internalEdges]
      _ = _ := Finset.sum_union hdis
  have hp : (∑ i ∈ P, (S.filter (T.Adj i)).card) ≤ P.card*q := by
    simpa using Finset.sum_le_sum hlocalP
  have hr : W+(∑ i ∈ R, (S.filter (T.Adj i)).card) ≤ R.card*(q+1) := by
    calc
      _ = ∑ i ∈ R, (((O i).filter fun j => j ∉ P).card+
          (S.filter (T.Adj i)).card) := by rw [Finset.sum_add_distrib]
      _ ≤ ∑ _i ∈ R, (q+1) := Finset.sum_le_sum hlocalR
      _ = _ := by simp
  change W+(P.card+R.card).choose 2 ≤ _
  rw [hs]
  have hh := Nat.add_le_add hp hr
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_comm] using hh

theorem positive_guards_disjoint {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    Disjoint (positiveTargets T label F A G q x hr)
      (tolerantGuards T label F A G q x) := by
  apply Finset.disjoint_left.mpr
  intro i hiP hiR
  have hone : (missingTargets F A x i).card = 1 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hiP).1).2.1
  have hempty : missingTargets F A x i = ∅ :=
    (Finset.mem_filter.mp hiR).2.1
  simp only [hempty, Finset.card_empty] at hone
  omega

theorem positive_gate_true {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (j : Fin k) (hj : j ∈ positiveTargets T label F A G q x hr)
    (c : Fin r) : F G (recursiveChild x j c) = true := by
  obtain ⟨hjT, hpass⟩ := Finset.mem_filter.mp hj
  by_cases hc : c = missingWitness F A x hr j
  · simpa only [hc] using hpass
  · exact hF.accepts_of_le hGA
      (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hjT).2.1 c hc)

/-- Ordinary arcs outside P consume both the old external-guard budget
and the remaining outgoing budget of P union R. -/
theorem ordinary_outside_positive_bound {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    let R := tolerantGuards T label F A G q x
    let P := positiveTargets T label F A G q x hr
    (∑ i ∈ R, ((ordinaryFailed T label F A G x i).filter fun j => j ∉ P).card) ≤
      positiveResidual q P.card R.card := by
  let R := tolerantGuards T label F A G q x
  let P := positiveTargets T label F A G q x hr
  let B := failedGuards T label F G x
  let O := ordinaryFailed T label F A G x
  let W := ∑ i ∈ R, ((O i).filter fun j => j ∉ P).card
  have hinside (i : Fin k) : (P ∪ R).filter (T.Adj i) ⊆ B i := by
    intro j hj
    obtain ⟨hjS, hij⟩ := Finset.mem_filter.mp hj
    apply (mem_failedGuards T label F G x i j).mpr
    refine ⟨hij, ?_⟩
    rcases Finset.mem_union.mp hjS with hjP | hjR
    · exact positive_gate_true T label F hF A G hGA q x hr j hjP _
    · exact hF.accepts_of_le hGA
        ((missingTargets_empty F A x j).mp (Finset.mem_filter.mp hjR).2.1 _)
  have hP : ∀ i ∈ P, (B i).card ≤ q := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2
  have hR : ∀ i ∈ R, (B i).card = q+1 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.2
  have hOR : ∀ i, ∀ j ∈ O i, j ∉ R := by
    intro i j hj hjR
    have hf := (Finset.mem_filter.mp hj).2
    have ht := (missingTargets_empty F A x j).mp
      (Finset.mem_filter.mp hjR).2.1 (label i j)
    simp only [ht, Bool.true_eq_false] at hf
  have hb := tournament_outside_budget T P R B O q
    (positive_guards_disjoint T label F A G q x hr) hinside hP hR
    (fun _ => Finset.filter_subset _ _) hOR
  have hW : W ≤ ordinaryTotal T label F A G q x := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hWM : W ≤ externalSlots q R.card :=
    hW.trans ((ordinary_counts T label F hF A G hGA q x).2.trans (min_le_right _ _))
  change W ≤ positiveResidual q P.card R.card
  unfold positiveResidual
  exact le_min hWM (by change W+_ ≤ _ at hb; omega)

/-- Counting arcs into P by the ordinary source rows gives at most u*n
copies.  The other copies use the residual outgoing budget. -/
theorem ordinary_positive_total_bound {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    let R := tolerantGuards T label F A G q x
    let P := positiveTargets T label F A G q x hr
    let OG := ordinaryGuards T label F A G q x
    ordinaryTotal T label F A G q x ≤
      positiveResidual q P.card R.card+OG.card*P.card := by
  let R := tolerantGuards T label F A G q x
  let P := positiveTargets T label F A G q x hr
  let OG := ordinaryGuards T label F A G q x
  let O := ordinaryFailed T label F A G x
  let W := ∑ i ∈ R, ((O i).filter fun j => j ∉ P).card
  let X := ∑ i ∈ R, ((O i).filter fun j => j ∈ P).card
  have hpart : W+X = ordinaryTotal T label F A G q x := by
    calc
      _ = ∑ i ∈ R, (((O i).filter fun j => j ∉ P).card+
          ((O i).filter fun j => j ∈ P).card) := by rw [Finset.sum_add_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        change ((O i).filter fun j => j ∉ P).card+
          ((O i).filter fun j => j ∈ P).card = (O i).card
        have hh := Finset.card_filter_add_card_filter_not (s := O i) (fun j => j ∈ P)
        omega
  have hXsum : (∑ i ∈ OG, ((O i).filter fun j => j ∈ P).card) = X := by
    change (∑ i ∈ R.filter fun i => (O i).Nonempty,
      ((O i).filter fun j => j ∈ P).card) = _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hn : (O i).Nonempty
    · rw [if_pos hn]
    · have hz : O i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        exact hn ⟨j, hj⟩
      rw [if_neg hn, hz, Finset.filter_empty, Finset.card_empty]
  have hX : X ≤ OG.card*P.card := by
    rw [← hXsum]
    calc
      _ ≤ ∑ _i ∈ OG, P.card := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.card_le_card (by intro j hj; exact (Finset.mem_filter.mp hj).2)
      _ = _ := by simp
  have hW : W ≤ positiveResidual q P.card R.card :=
    ordinary_outside_positive_bound T label F hF A G hGA q x hr
  change ordinaryTotal T label F A G q x ≤ _
  rw [← hpart]
  exact Nat.add_le_add hW hX

/-- The ordinary derivative union has the old L-arc cover and a second
cover using W outside arcs plus one missing child per used positive head.
Only actual incoming arcs need to satisfy the derivative bound. -/
theorem ordinary_positive_union_card {n k r : ℕ} {I α : Type}
    [DecidableEq α]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (D : Fin k → Fin r → Finset α) (c : ℕ)
    (hD : ∀ i ∈ tolerantGuards T label F A G q x,
      ∀ j ∈ ordinaryFailed T label F A G x i, (D j (label i j)).card ≤ c) :
    let R := tolerantGuards T label F A G q x
    let P := positiveTargets T label F A G q x hr
    let L := ordinaryTotal T label F A G q x
    (R.biUnion fun i => (ordinaryFailed T label F A G x i).biUnion fun j =>
      D j (label i j)).card ≤
      min L (positiveResidual q P.card R.card+P.card)*c := by
  let R := tolerantGuards T label F A G q x
  let P := positiveTargets T label F A G q x hr
  let O := ordinaryFailed T label F A G x
  let L := ordinaryTotal T label F A G q x
  let W := ∑ i ∈ R, ((O i).filter fun j => j ∉ P).card
  let V := R.biUnion fun i => (O i).biUnion fun j => D j (label i j)
  let VO := R.biUnion fun i => ((O i).filter fun j => j ∉ P).biUnion fun j =>
    D j (label i j)
  let VP := R.biUnion fun i => ((O i).filter fun j => j ∈ P).biUnion fun j =>
    D j (label i j)
  have hVarc : V.card ≤ L*c := by
    calc
      _ ≤ ∑ i ∈ R, ∑ j ∈ O i, (D j (label i j)).card :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
      _ ≤ ∑ i ∈ R, ∑ _j ∈ O i, c :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hD i hi j hj
      _ = L*c := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, ← Finset.sum_mul]; rfl
  have hVO : VO.card ≤ W*c := by
    calc
      _ ≤ ∑ i ∈ R, ∑ j ∈ (O i).filter (fun j => j ∉ P),
          (D j (label i j)).card :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
      _ ≤ ∑ i ∈ R, ∑ _j ∈ (O i).filter (fun j => j ∉ P), c :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
          hD i hi j (Finset.mem_filter.mp hj).1
      _ = W*c := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, ← Finset.sum_mul]; rfl
  have hVP : VP.card ≤ P.card*c := by
    apply SensitivitySharedGuardHead.used_head_union_card R O P label
      (missingWitness F A x hr) D c
    · intro i hi j hj hjP
      exact missingWitness_unique F A x hr j
        (Finset.mem_filter.mp (Finset.mem_filter.mp hjP).1).2.1 _
        (Finset.mem_filter.mp hj).2
    · intro i hi j hj hjP
      exact hD i hi j hj
  have hsplit : V ⊆ VO ∪ VP := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    by_cases hjP : j ∈ P
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨hj, hjP⟩, hp⟩⟩
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨hj, hjP⟩, hp⟩⟩
  have hW : W ≤ positiveResidual q P.card R.card :=
    ordinary_outside_positive_bound T label F hF A G hGA q x hr
  have hVhead : V.card ≤ (positiveResidual q P.card R.card+P.card)*c := by
    calc
      _ ≤ VO.card+VP.card := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
      _ ≤ W*c+P.card*c := Nat.add_le_add hVO hVP
      _ = (W+P.card)*c := by ring
      _ ≤ _ := Nat.mul_le_mul_right c (Nat.add_le_add_right hW _)
  change V.card ≤ _
  rw [min_mul]
  exact le_min hVarc hVhead

end
end SensitivityOrdinaryGuard
end



/- Component: Research.InternalGuardHeads -/
section
/-! Internal failed guards are indexed by arcs in the accepted estimate.
Their actual coordinate union also has a cover indexed by head and child.
This module changes only that union bound; the Boolean lift is unchanged. -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators

namespace SensitivitySharedGuardHead
noncomputable section

/-- A union indexed by source/head arcs occupies at most one derivative
set per head and child color.  This finite-set lemma has no Boolean or
tournament assumptions and can also be reused in finer guard splits. -/
theorem internal_by_head_card {J α : Type} [DecidableEq J] [DecidableEq α]
    {r : ℕ} (S : Finset J) (B : J → Finset J)
    (label : J → J → Fin r) (D : J → Fin r → Finset α) (e : ℕ)
    (hD : ∀ j ∈ S, ∀ c, (D j c).card ≤ e) :
    (S.biUnion fun i => (B i).biUnion fun j =>
      if j ∈ S then D j (label i j) else ∅).card ≤ (r*S.card)*e := by
  let V := S.biUnion fun i => (B i).biUnion fun j =>
    if j ∈ S then D j (label i j) else ∅
  let H := S.biUnion fun j => (Finset.univ : Finset (Fin r)).biUnion fun c => D j c
  have hVH : V ⊆ H := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    by_cases hin : j ∈ S
    · rw [if_pos hin] at hp
      exact Finset.mem_biUnion.mpr ⟨j, hin, Finset.mem_biUnion.mpr
        ⟨label i j, Finset.mem_univ _, hp⟩⟩
    · simp only [if_neg hin, Finset.notMem_empty] at hp
  have hH : H.card ≤ S.card*(r*e) := by
    apply card_biUnion_le_mul
    intro j hj
    have hh := card_biUnion_le_mul (Finset.univ : Finset (Fin r))
      (D j) e (fun c _ => hD j hj c)
    simpa only [Finset.card_univ, Fintype.card_fin] using hh
  change V.card ≤ _
  exact (Finset.card_le_card hVH).trans (by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hH)













/- The accepted coupled-pair proof is retained through the derivative cover
and target charge; only its guard-union cardinality estimate is replaced. -/



end
end SensitivitySharedGuardHead

namespace SensitivityNQ
noncomputable section
variable {n : ℕ}













end
end SensitivityNQ
end



/- Component: Research.NonordinaryGuardHeads -/
section
/-! The nonordinary failed-guard union has an external arc count and an
internal head-child cover.  This is the internal cap needed by the finer
ordinary/positive-target-head transfer. -/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open SensitivityOrdinaryGuard
open scoped Classical BigOperators

namespace SensitivitySharedGuardHead
noncomputable section

theorem nonordinary_guardUnion_card {n k r : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (Y : Fin n → Fin n → ℕ) (hY : PairBound F true Y)
    (x : ((Fin k × Fin r) × I) → Bool) :
    let R := tolerantGuards T label F A G q x
    let L := ordinaryTotal T label F A G q x
    let M := R.card*(q+1)-R.card.choose 2
    (R.biUnion fun i => (failedGuards T label F G x i).biUnion fun j =>
      if F A (recursiveChild x j (label i j)) = false then ∅
        else childJointChanges F G A x j (label i j)).card ≤
      (M-L+min (R.card.choose 2) (r*R.card))*Y G A := by
  let R := tolerantGuards T label F A G q x
  let B := failedGuards T label F G x
  let p := fun i j => F A (recursiveChild x j (label i j)) = false
  let D := childJointChanges F G A x
  let L := ordinaryTotal T label F A G q x
  let M := R.card*(q+1)-R.card.choose 2
  let X := ∑ i ∈ R, ∑ j ∈ B i,
    if j ∈ R then 0 else if p i j then 0 else 1
  let VN := R.biUnion fun i => (B i).biUnion fun j =>
    if p i j then ∅ else D j (label i j)
  let VI := R.biUnion fun i => (B i).biUnion fun j =>
    if j ∈ R then D j (label i j) else ∅
  let VE := R.biUnion fun i => (B i).biUnion fun j =>
    if j ∈ R then ∅ else if p i j then ∅ else D j (label i j)
  have hA (j : Fin k) (hj : j ∈ R) (c : Fin r) :
      F A (recursiveChild x j c) = true :=
    (missingTargets_empty F A x j).mp (Finset.mem_filter.mp hj).2.1 c
  have hnotOrd (i j : Fin k) (hj : j ∈ R) : ¬p i j := by
    intro hp
    have hf : F A (recursiveChild x j (label i j)) = false := hp
    simp only [hA j hj (label i j), Bool.true_eq_false] at hf
  have hD (j : Fin k) (hj : j ∈ R) (c : Fin r) : (D j c).card ≤ Y G A := by
    change (childJointChanges F G A x j c).card ≤ Y G A
    rw [childJointChanges_card]
    exact hY _ _ hGA _ (hF.accepts_of_le hGA (hA j hj c)) (hA j hj c)
  have hordinaryCount : (∑ i ∈ R, ∑ j ∈ B i, if p i j then 1 else 0) = L := by
    simpa only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] using
      ordinary_weight_identity T label F A G q x 1 0
  have hexternalCount : (∑ i ∈ R, ∑ j ∈ B i, if j ∈ R then 0 else 1) = M := by
    simpa only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] using
      guard_charge T label F hF A G hGA q x 1 0
  have hpartition : L+X=M := by
    calc
      L+X = (∑ i ∈ R, ∑ j ∈ B i, if p i j then 1 else 0)+X := by
        rw [hordinaryCount]
      _ = ∑ i ∈ R, ∑ j ∈ B i,
          ((if p i j then 1 else 0)+
            (if j ∈ R then 0 else if p i j then 0 else 1)) := by
        simp only [X, Finset.sum_add_distrib]
      _ = ∑ i ∈ R, ∑ j ∈ B i, if j ∈ R then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hin : j ∈ R
        · simp only [if_pos hin, if_neg (hnotOrd i j hin), Nat.zero_add]
        · by_cases ho : p i j
          · simp only [if_neg hin, if_pos ho, Nat.add_zero]
          · simp only [if_neg hin, if_neg ho, Nat.zero_add]
      _ = M := hexternalCount
  have hX : X=M-L := by omega
  have hsplit : VN ⊆ VE ∪ VI := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j, hj, hz⟩ := Finset.mem_biUnion.mp hz
    by_cases ho : p i j
    · simp only [if_pos ho, Finset.notMem_empty] at hz
    · rw [if_neg ho] at hz
      by_cases hin : j ∈ R
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr
          ⟨j, hj, by simpa only [if_pos hin] using hz⟩⟩
      · apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr
          ⟨j, hj, by simpa only [if_neg hin, if_neg ho] using hz⟩⟩
  have hweight : (∑ i ∈ R, ∑ j ∈ B i,
      if j ∈ R then 0 else if p i j then 0 else Y G A) = X*Y G A := by
    simp only [X, Finset.sum_mul, ite_mul, Nat.zero_mul, Nat.one_mul]
  have hVE : VE.card ≤ X*Y G A := by
    apply le_trans Finset.card_biUnion_le
    apply le_trans (Finset.sum_le_sum (fun i hi => Finset.card_biUnion_le))
    apply le_trans (Finset.sum_le_sum ?_) hweight.le
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    change (if j ∈ R then ∅ else if p i j then ∅ else D j (label i j)).card ≤
      if j ∈ R then 0 else if p i j then 0 else Y G A
    by_cases hin : j ∈ R
    · simp only [if_pos hin, Finset.card_empty]
      exact Nat.zero_le _
    · by_cases ho : p i j
      · simp only [if_neg hin, if_pos ho, Finset.card_empty]
        exact Nat.zero_le _
      · simp only [if_neg hin, if_neg ho, D, childJointChanges_card]
        have hto : F A (recursiveChild x j (label i j)) = true := by
          cases hh : F A (recursiveChild x j (label i j))
          · exact False.elim (ho hh)
          · rfl
        exact hY _ _ hGA _ ((mem_failedGuards T label F G x i j).mp hj).2 hto
  have hVIarc : VI.card ≤ R.card.choose 2*Y G A := by
    apply le_trans Finset.card_biUnion_le
    apply le_trans (Finset.sum_le_sum (fun i hi => Finset.card_biUnion_le))
    apply le_trans (Finset.sum_le_sum ?_)
      (by simpa only [Nat.mul_zero, Nat.zero_add] using
        (guard_charge T label F hF A G hGA q x 0 (Y G A)).le)
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    change (if j ∈ R then D j (label i j) else ∅).card ≤
      if j ∈ R then Y G A else 0
    by_cases hin : j ∈ R
    · simpa only [if_pos hin] using hD j hin (label i j)
    · simp only [if_neg hin, Finset.card_empty]
      exact Nat.zero_le _
  have hVIhead : VI.card ≤ (r*R.card)*Y G A :=
    internal_by_head_card R B label D (Y G A) hD
  have hVI : VI.card ≤ min (R.card.choose 2) (r*R.card)*Y G A := by
    by_cases hle : R.card.choose 2 ≤ r*R.card
    · simpa only [min_eq_left hle] using hVIarc
    · have hle' : r*R.card ≤ R.card.choose 2 := by omega
      simpa only [min_eq_right hle'] using hVIhead
  have hh := (Finset.card_le_card hsplit).trans
    ((Finset.card_union_le VE VI).trans (Nat.add_le_add hVE hVI))
  change VN.card ≤ _
  simpa only [hX, Nat.add_mul] using hh

end
end SensitivitySharedGuardHead
end



/- Component: Research.OrdinaryGuardPositiveStage -/
section
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 30000

open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators

namespace SensitivityOrdinaryGuard
noncomputable section

theorem ordinary_dedup_pair_zero {n k r q v : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r) (hDefect : DefectBound T label q v)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (Z Y : Fin n → Fin n → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hGA : Gi ≤ Ai)
    (hZle : Z Gj Aj ≤ Z Ai Aj) (hYle : Y Gj Aj ≤ Y Gj Gi)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T label F Ai Gi q x = false)
    (hx' : tolerantFamily T label F Aj Gj q x = false) :
    jointSensitivityAt (tolerantFamily T label F Ai Gi q)
      (tolerantFamily T label F Aj Gj q) x ≤
      ordinaryDedupInternalCost r q v (Z Ai Aj) (Z Gj Aj) (Y Gj Gi) (Y Gj Aj) := by
  let TC := tolerantTargets T label F Aj Gj q x
  let GC := tolerantGuards T label F Aj Gj q x
  let OG := ordinaryGuards T label F Aj Gj q x
  let L := ordinaryTotal T label F Aj Gj q x
  let P := positiveTargets T label F Aj Gj q x hr
  let tw := missingWitness F Aj x hr
  let B := failedGuards T label F Gj x
  let U := splitTargetChanges F Ai Aj Gj Gj x TC tw
  let V := GC.biUnion fun i => (B i).biUnion fun j =>
    if F Aj (recursiveChild x j (label i j)) = false
      then childJointChanges F Gj Gi x j (label i j)
      else childJointChanges F Gj Aj x j (label i j)
  have hGJA : Gj ≤ Aj := hG.trans (hGA.trans hA)
  have hweakguard : ∀ i ∈ GC, ∀ j ∈ B i,
      F Gi (recursiveChild x j (label i j)) = true := by
    intro i hi j hj
    have he := tolerant_guard_sets_eq T label F hF Ai Aj Gi Gj hA hG x q hx hi
    have hj' : j ∈ failedGuards T label F Gi x i := by rw [he]; exact hj
    exact ((mem_failedGuards T label F Gi x i j).mp hj').2
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T label F Ai Gi q (flip x {p}) ≠ tolerantFamily T label F Ai Gi q x ∧
      tolerantFamily T label F Aj Gj q (flip x {p}) ≠ tolerantFamily T label F Aj Gj q x) ⊆
      U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)}) = true := by
      cases hy : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)})
      · exact False.elim (hc.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi⟩ := (tolerantFamily_true T label F Aj Gj q _).mp hon
    have hoff := (tolerantFamily_false T label F Aj Gj q x).mp hx' i
    rcases tolerant_repair_cases T label F Aj Gj q x i j c a hoff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, hcl, hgon, hgoff⟩
    · subst j
      have hcw := missingWitness_unique F Aj x hr i (Finset.mem_filter.mp hit).2.1 c htoff
      have hwo : F Ai (recursiveChild x i c) = false := by
        rw [hcw]
        exact tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
          (le_refl q) hr hx hit
      have hwn := hF.accepts_of_le hA hton
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
          F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
        simp [hwo, hwn, htoff, hton]
      by_cases hgo : F Gj (recursiveChild x i (tw i)) = true
      · rw [if_pos hgo]
        simpa [childJointChanges, tw, hcw] using hn
      · rw [if_neg hgo]
        apply Finset.mem_inter.mpr
        constructor
        · simpa [childJointChanges, tw, hcw] using hn
        · have hgoff : F Gj (recursiveChild x i c) = false := by
            simpa only [tw, ← hcw, Bool.not_eq_true] using hgo
          have hgn := hF.accepts_of_le hGJA hton
          have hn0 : F Gj (flip (recursiveChild x i c) {a}) ≠ F Gj (recursiveChild x i c) ∧
              F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
            simp [hgoff, hgn, htoff, hton]
          simpa [childJointChanges, tw, hcw] using hn0
    · subst c
      have hj : j ∈ B i := (mem_failedGuards T label F Gj x i j).mpr ⟨hij, hgon⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hig, Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩⟩
      by_cases hfalse : F Aj (recursiveChild x j (label i j)) = false
      · rw [if_pos hfalse]
        have hwo := hweakguard i hig j hj
        have hwf := hF.rejects_of_le hG hgoff
        have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gj (recursiveChild x j (label i j)) ∧
            F Gi (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gi (recursiveChild x j (label i j)) := by simp [hgon, hgoff, hwo, hwf]
        simpa [childJointChanges] using hn
      · rw [if_neg hfalse]
        have hto : F Aj (recursiveChild x j (label i j)) = true := by
          cases hh : F Aj (recursiveChild x j (label i j)) <;> simp_all
        have htf := hF.rejects_of_le hGJA hgoff
        have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Gj (recursiveChild x j (label i j)) ∧
            F Aj (flip (recursiveChild x j (label i j)) {a}) ≠
              F Aj (recursiveChild x j (label i j)) := by simp [hgon, hgoff, hto, htf]
        simpa [childJointChanges] using hn
  have hTU : TC.card+OG.card < v :=
    targets_ordinary_card T label hDefect F hF Aj Gj hGJA x hr
  have hTC : TC.card ≤ v-1-OG.card := by omega
  have hP : P.card ≤ TC.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hU : U.card ≤ P.card*Z Ai Aj+(v-1-OG.card-P.card)*Z Gj Aj := by
    have hh := splitTargetChanges_card_count F Ai Aj Gj Gj hA hGJA Z hZ x TC tw
      (fun i hi => tolerant_target_weak_false T label F hF Ai Aj Gi Gj hA hG x
        (le_refl q) hr hx hi)
      (fun i hi => missingWitness_false F Aj x hr i (Finset.mem_filter.mp hi).2.1)
      (fun i hi hn => Bool.eq_false_iff.mpr hn)
    have hU0 : U.card ≤ P.card*Z Ai Aj+(TC.card-P.card)*Z Gj Aj := by
      simpa only [U, P, positiveTargets, TC, tw, min_eq_right hZle] using hh
    exact hU0.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hTC P.card)) _)
  let VO := GC.biUnion fun i =>
    (ordinaryFailed T label F Aj Gj x i).biUnion fun j =>
      childJointChanges F Gj Gi x j (label i j)
  let VN := GC.biUnion fun i => (B i).biUnion fun j =>
    if F Aj (recursiveChild x j (label i j)) = false then ∅
      else childJointChanges F Gj Aj x j (label i j)
  have hVO : VO.card ≤
      min L (positiveResidual q P.card GC.card+P.card)*Y Gj Gi := by
    apply ordinary_positive_union_card T label F hF Aj Gj hGJA q x hr
      (childJointChanges F Gj Gi x) (Y Gj Gi)
    intro i hi j hj
    have hjB := (Finset.mem_filter.mp hj).1
    rw [childJointChanges_card]
    exact hY _ _ hG _ ((mem_failedGuards T label F Gj x i j).mp hjB).2
      (hweakguard i hi j hjB)
  have hVN : VN.card ≤
      (externalSlots q GC.card-L+min (GC.card.choose 2) (r*GC.card))*Y Gj Aj :=
    SensitivitySharedGuardHead.nonordinary_guardUnion_card T label F hF Aj Gj hGJA q Y hY x
  have hVsplit : V ⊆ VO ∪ VN := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    by_cases ho : F Aj (recursiveChild x j (label i j)) = false
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨hj, ho⟩, by simpa only [if_pos ho] using hp⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr
        ⟨j, hj, by simpa only [if_neg ho] using hp⟩⟩
  have hV : V.card ≤
      min L (positiveResidual q P.card GC.card+P.card)*Y Gj Gi+
        (externalSlots q GC.card-L+min (GC.card.choose 2) (r*GC.card))*Y Gj Aj :=
    (Finset.card_le_card hVsplit).trans
      ((Finset.card_union_le VO VN).trans (Nat.add_le_add hVO hVN))
  have hcounts := ordinary_counts T label F hF Aj Gj hGJA q x
  change OG.card ≤ L ∧ L ≤ ordinaryLimit q GC.card OG.card at hcounts
  have hLP : L ≤ positiveResidual q P.card GC.card+OG.card*P.card :=
    ordinary_positive_total_bound T label F hF Aj Gj hGJA q x hr
  have hLD : L ≤ dedupLimit q P.card GC.card OG.card := le_min hcounts.2 hLP
  have hnum := charge_le_dedupCost (fun m => min (m.choose 2) (r*m))
    q v (Z Ai Aj) (Z Gj Aj) (Y Gj Gi) (Y Gj Aj) P.card GC.card OG.card L
    (positiveTargets_card T label F hF Aj Gj hGJA q x hr)
    (guards_card T label F hF Aj Gj hGJA q x)
    (Finset.card_le_card (ordinaryGuards_subset T label F Aj Gj q x))
    (positiveTargets_guards_coupling T label F hF Aj Gj hGJA q x hr)
    (by omega) hcounts.1 hLD hYle
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  change jointSensitivityAt _ _ x ≤ _ at hh
  have hcharges := Nat.add_le_add hU hV
  exact hh.trans (hcharges.trans (by
    simpa only [ordinaryDedupInternalCost, Nat.add_assoc] using hnum))

end
end SensitivityOrdinaryGuard

namespace SensitivityNQ
noncomputable section
variable {n : ℕ}

def rawZeroDedupBoth (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  if 3 ≤ i.val ∧ C.tol i = C.tol j then
    min (rawZeroCoupled k t v C Z Y i j)
      (SensitivityOrdinaryGuard.ordinaryDedupInternalCost 2 (C.tol j) (v (C.tol j))
        (Z (C.target i) (C.target j)) (Z (C.gate j) (C.target j))
        (Y (C.gate j) (C.gate i)) (Y (C.gate j) (C.target j)))
  else rawZeroCoupled k t v C Z Y i j

theorem stage_zero_dedup_both {k t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T 2 t) (ht : 4 ≤ t)
    (v : ℕ → ℕ) (hv : v 0 = t) (C : Recipe n) (hC : C.Valid)
    (hDefect : ∀ j : Fin n, 3 ≤ j.val → 0 < C.tol j →
      DefectBound T L.label (C.tol j) (v (C.tol j)))
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (Z Y : Fin n → Fin n → ℕ) (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (hc : Compatible C Z Y) :
    PairBound (stage T L.label C F) false (rawZeroDedupBoth k t v C Z Y) := by
  have hold := stage_zero_coupled T L ht v C hC hDefect F hF Z Y hZ hY hc
  intro i j hij x hx hx'
  unfold rawZeroDedupBoth
  split_ifs with he
  · apply le_min (hold i j hij x hx hx')
    have hj : 3 ≤ j.val := by omega
    have hpair := hC.2.2 i j hij he.1
    have hcompat := hc i j hij he.1
    have hd : DefectBound T L.label (C.tol j) (v (C.tol j)) := by
      by_cases hq : C.tol j = 0
      · rw [hq, hv]
        exact labeling_defect_zero T L
      · exact hDefect j hj (by omega)
    have hi3 : ¬i.val < 3 := by omega
    have hj3 : ¬j.val < 3 := by omega
    simp only [stage, if_neg hi3, if_neg hj3] at hx hx' ⊢
    simpa only [he.2] using
      (SensitivityOrdinaryGuard.ordinary_dedup_pair_zero T L.label hd F hF (by decide)
        Z Y hZ hY (C.target i) (C.target j) (C.gate i) (C.gate j)
        (hC.1 hij) hpair.1 hpair.2.2 hcompat.1 hcompat.2 x
        (by simpa only [he.2] using hx) hx')
  · exact hold i j hij x hx hx'

theorem rawZeroDedupBoth_mul (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (w : ℕ) (i j : Fin n) :
    rawZeroDedupBoth k t v C (fun i j => Z i j*w) (fun i j => Y i j*w) i j =
      rawZeroDedupBoth k t v C Z Y i j*w := by
  unfold rawZeroDedupBoth
  split_ifs <;> simp only [rawZeroCoupled_mul,
    SensitivityOrdinaryGuard.ordinaryDedupInternalCost, SensitivityOrdinaryGuard.dedupCost_mul, min_mul]

end
end SensitivityNQ
end



/- Component: Research.SourceCombinedStage -/
section
set_option autoImplicit false
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075 SensitivityQ
open scoped Classical
namespace SensitivityNQ
noncomputable section
variable {n : ℕ}

def rawZeroSourceCombined (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  min (rawZeroSourceFull k t v w C Z Y i j) (rawZeroDedupBoth k t v C Z Y i j)

theorem stage_zero_source_combined {k t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T 2 t) (ht : 4 ≤ t)
    (v : ℕ → ℕ) (hv : v 0 = t) (w : ℕ) (hw : 4 ≤ w)
    (hSource : SensitivitySourceZero.SourceBound T L.label w)
    (C : Recipe n) (hC : C.Valid)
    (hDefect : ∀ j : Fin n, 3 ≤ j.val → 0 < C.tol j →
      DefectBound T L.label (C.tol j) (v (C.tol j)))
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (Z Y : Fin n → Fin n → ℕ) (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (hc : Compatible C Z Y) :
    PairBound (stage T L.label C F) false (rawZeroSourceCombined k t v w C Z Y) := by
  have hfull := stage_zero_source_full T L ht v hv w hw hSource C hC hDefect
    F hF Z Y hZ hY hc
  have hdedup := stage_zero_dedup_both T L ht v hv C hC hDefect F hF Z Y hZ hY hc
  intro i j hij x hx hx'
  exact le_min (hfull i j hij x hx hx') (hdedup i j hij x hx hx')

theorem rawZeroSourceCombined_mul (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (s : ℕ) (i j : Fin n) :
    rawZeroSourceCombined k t v w C (fun i j => Z i j*s) (fun i j => Y i j*s) i j =
      rawZeroSourceCombined k t v w C Z Y i j*s := by
  simp only [rawZeroSourceCombined, rawZeroSourceFull_mul, rawZeroDedupBoth_mul, min_mul]

end
end SensitivityNQ
end



/- Component: Research.SourceCombinedPeriodicAPI -/
section
set_option autoImplicit false
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators
namespace SensitivitySourceCombinedPeriodic
noncomputable section

theorem profile_step_bounds {n k h q : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (L : Labeling T 2 q) (hq : 4 ≤ q) (v : ℕ → ℕ) (hv : v 0 = q) (w : ℕ) (hw : 4 ≤ w)
    (hSource : SensitivitySourceZero.SourceBound T L.label w)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = h)
    (A : SensitivityNQ.Recipe n) (hA : A.Valid)
    (hDefect : ∀ j : Fin n, 3 ≤ j.val → 0 < A.tol j →
      SensitivityQ.DefectBound T L.label (A.tol j) (v (A.tol j)))
    (Z Y Z' Y' : Fin n → Fin n → ℕ) (hc : SensitivityNQ.Compatible A Z Y)
    (cz : ∀ i j : Fin n, i ≤ j → ∃ a b, i ≤ a ∧ a ≤ b ∧ b ≤ j ∧ SensitivityNQ.rawZeroSourceCombined k q v w A Z Y a b ≤ Z' i j)
    (cy : ∀ i j : Fin n, i ≤ j → ∃ a b, i ≤ a ∧ a ≤ b ∧ b ≤ j ∧ SensitivityNQ.rawOne h A Z Y a b ≤ Y' i j)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F) (u : ℕ)
    (hz : PairBound F false (fun i j => Z i j*u))
    (hy : PairBound F true (fun i j => Y i j*u)) :
    PairBound (SensitivityNQ.stage T L.label A F) false (fun i j => Z' i j*u) ∧
    PairBound (SensitivityNQ.stage T L.label A F) true (fun i j => Y' i j*u) := by
  have hcu : SensitivityNQ.Compatible A (fun i j => Z i j*u) (fun i j => Y i j*u) := by
    intro i j hij hi
    exact ⟨Nat.mul_le_mul_right u (hc i j hij hi).1, Nat.mul_le_mul_right u (hc i j hij hi).2⟩
  have hn := SensitivityNQ.stage_nested T L.label A hA F hF
  constructor
  · apply pairBound_containment _ hn false
      (SensitivityNQ.rawZeroSourceCombined k q v w A (fun i j => Z i j*u) (fun i j => Y i j*u)) _
      (SensitivityNQ.stage_zero_source_combined T L hq v hv w hw hSource A hA hDefect F hF _ _ hz hy hcu)
    intro i j hij
    obtain ⟨a,b,hia,hab,hbj,hh⟩ := cz i j hij
    refine ⟨a,b,hia,hab,hbj,?_⟩
    rw [SensitivityNQ.rawZeroSourceCombined_mul]
    exact Nat.mul_le_mul_right u hh
  · apply pairBound_containment _ hn true
      (SensitivityNQ.rawOne h A (fun i j => Z i j*u) (fun i j => Y i j*u)) _
      (SensitivityNQ.stage_one T L.label h ho A hA F hF _ _ hz hy)
    intro i j hij
    obtain ⟨a,b,hia,hab,hbj,hh⟩ := cy i j hij
    refine ⟨a,b,hia,hab,hbj,?_⟩
    rw [SensitivityNQ.rawOne_mul]
    exact Nat.mul_le_mul_right u hh

def stage_blocks {N k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (C : SensitivityNQ.Recipe N)
    (F : Fin N → (I → Bool) → Bool) {n : ℕ} (w : Blocks F n) :
    Blocks (SensitivityNQ.stage T label C F) (k*n) where
  zero q := SensitivityNQ.stage_zero_input T label C F w.zero q
  sets i := rowLift (finProdFinEquiv.symm i).1 (w.sets (finProdFinEquiv.symm i).2)
  nonempty i := by
    obtain ⟨a,ha⟩ := w.nonempty (finProdFinEquiv.symm i).2
    exact ⟨(((finProdFinEquiv.symm i).1,0),a), (mem_rowLift _ _ _).mpr ⟨rfl,ha⟩⟩
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hi := (mem_rowLift _ _ _).mp hp
    have hj := (mem_rowLift _ _ _).mp hq
    have he : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 :=
      hi.1.symm.trans hj.1
    have hne : (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 := by
      intro he'
      exact hij (finProdFinEquiv.symm.injective (Prod.ext he he'))
    exact Finset.disjoint_left.mp (w.disjoint hne) hi.2 hj.2
  on q i := SensitivityNQ.stage_rowLift T label C F w.zero _
    (fun j => w.on j _) _ q

end
end SensitivitySourceCombinedPeriodic
end



/- Component: Research.SourceLabelBridge -/
section
set_option autoImplicit false
open OAI.Paper320 Sensitivity205
open scoped Classical

namespace SensitivitySourceLabelBridge
noncomputable section

theorem labeling_of_raw {k t w : ℕ} (T : Tournament k) (J : Fin 5 → ℕ)
    (hJ : J 0 = t) (a : Fin k → Fin k → Fin 2)
    (hdefect : ∀ q : Fin 5, SensitivityQ.DefectBound T a q.val (J q))
    (hsource : SensitivitySourceZero.SourceBound T a w) :
    ∃ L : Labeling T 2 t,
      (∀ q : Fin 5, SensitivityQ.DefectBound T L.label q.val (J q)) ∧
      SensitivitySourceZero.SourceBound T L.label w := by
  refine ⟨⟨a, ?_⟩, hdefect, hsource⟩
  intro I colors hcoh
  have hh : I.card < J 0 := hdefect 0 I colors (by
    intro i hi
    have he : (I.filter fun j => T.Adj i j ∧ a i j ≠ colors j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨hj, hij, hne⟩ := Finset.mem_filter.mp hj
      exact hne (hcoh i hi j hj hij)
    rw [he]
    exact Nat.zero_le _)
  simpa only [hJ] using hh

end
end SensitivitySourceLabelBridge
end



/- Component: Research.SourceLabelsBelow14567 -/
section
set_option autoImplicit false
open OAI.Paper320 Sensitivity205
open scoped Classical

namespace SensitivitySourceLabelsBelow14567
noncomputable section

def J : Fin 5 → ℕ := ![24,31,38,44,50]
def v : ℕ → ℕ
  | 0 => 24
  | 1 => 31
  | 2 => 38
  | 3 => 44
  | _ => 50

theorem cutoff_eq_v (q : Fin 5) : J q = v q.val := by fin_cases q <;> rfl

theorem labeling_exists {k d : ℕ} (T : Tournament k)
    (hodd : k = 2*d+1) (hdlo : 21 ≤ d) (hdhi : d ≤ 7283)
    (hout : ∀ i, (Finset.univ.filter (T.Adj i)).card = d) :
    ∃ L : Labeling T 2 24,
      (∀ q : Fin 5, SensitivityQ.DefectBound T L.label q.val (v q.val)) ∧
      SensitivitySourceZero.SourceBound T L.label 22 := by
  obtain ⟨a, hdefect, hsource⟩ :=
    SensitivitySourceLabeling14567.shared_labeling_source_below_14567_lll
      hodd hdlo hdhi T.Adj T.loopless (fun {_ _} h => T.edge_compl h) hout
  obtain ⟨L, hL, hS⟩ := SensitivitySourceLabelBridge.labeling_of_raw T J rfl a hdefect hsource
  refine ⟨L, ?_, hS⟩
  intro q
  rw [← cutoff_eq_v q]
  exact hL q

def tournament (d : ℕ) : Tournament (2*d+1) := cyclicTournament d

def cyclicLabeling (d : ℕ) (hdlo : 21 ≤ d) (hdhi : d ≤ 7283) :
    Labeling (tournament d) 2 24 :=
  Classical.choose (labeling_exists (tournament d) rfl hdlo hdhi
    (cyclicTournament_outdegree d))

theorem cyclic_defect (d : ℕ) (hdlo : 21 ≤ d) (hdhi : d ≤ 7283)
    (q : ℕ) (hq : q < 5) :
    SensitivityQ.DefectBound (tournament d) (cyclicLabeling d hdlo hdhi).label q (v q) :=
  (Classical.choose_spec (labeling_exists (tournament d) rfl hdlo hdhi
    (cyclicTournament_outdegree d))).1 ⟨q, hq⟩

theorem cyclic_source (d : ℕ) (hdlo : 21 ≤ d) (hdhi : d ≤ 7283) :
    SensitivitySourceZero.SourceBound (tournament d) (cyclicLabeling d hdlo hdhi).label 22 :=
  (Classical.choose_spec (labeling_exists (tournament d) rfl hdlo hdhi
    (cyclicTournament_outdegree d))).2

end
end SensitivitySourceLabelsBelow14567
end



/- Component: Research.SourceCombined14055P4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
open OAI.Paper320 Sensitivity205 Sensitivity20635 Sensitivity2075
open scoped Classical BigOperators
namespace SourceCombined14055P4
noncomputable section

abbrev N : ℕ := 16
abbrev K : ℕ := 14055
abbrev D : ℕ := 7027
abbrev t : ℕ := 24
abbrev w : ℕ := 22
abbrev R : ℕ := 61141556
abbrev C : ℕ := 47518144717110082135993943296909130163290926
def G : ℕ := K^4
abbrev output : Fin N := 0


def v : ℕ → ℕ
  | 0 => 24
  | 1 => 31
  | 2 => 38
  | 3 => 44
  | _ => 50

def periodTournament : Tournament K := cyclicTournament D
def periodLabeling : Labeling periodTournament 2 t := SensitivitySourceLabelsBelow14567.cyclicLabeling D (by decide +kernel) (by decide +kernel)
theorem source_bound : SensitivitySourceZero.SourceBound periodTournament periodLabeling.label w :=
  SensitivitySourceLabelsBelow14567.cyclic_source D (by decide +kernel) (by decide +kernel)

def VZ : Fin N → Fin N → ℕ := ![![47518144717110082135993943296909130163290926, 407251570856355077015422170417574428478855, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![0, 15951380967412634469290762746981449188860896, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 7975690483706317234645381373490724594430448, 27805680092608292129407648785231244924834, 24384327237487845819589028418793473675589, 1348540308066162927519618365512769282675, 1093411060594186204436837976869800762642, 838281813122209404084081846946852254276, 834680326527526516654150386101753621117, 36798432129568720840085214397181578972, 2245967311937524535079578658598265247, 381680204344614899874381912886590172, 308432361542795403340598363090296043, 1226175664895509019865306, 1000000000000000000000000, 1000000000000000000000000], ![0, 0, 0, 1379662257071838767852744531457323448725046, 24384327237487845819589028418793473675589, 1348540308066162927519618365512769282675, 1093411060594186204436837976869800762642, 838281813122209404084081846946852254276, 834680326527526516654150386101753621117, 36798432129568720840085214397181578972, 2245967311937524535079578658598265247, 381680204344614899874381912886590172, 308432361542795403340598363090296043, 1226175664895509019865306, 1000000000000000000000000, 1000000000000000000000000], ![0, 0, 0, 0, 998996833733884669368982201085822039479697, 1377691004970310637810550546924060123731, 1110901478736674645163455506644623295277, 838281813122209404084081846946852254276, 834680326527526516654150386101753621117, 36798432129568720840085214397181578972, 2245967311937524535079578658598265247, 381680204344614899874381912886590172, 308432361542795403340598363090296043, 88653018620081684679364695, 88426842955186189606730010, 88426842955186189606730010], ![0, 0, 0, 0, 0, 298157931883327013873180395482767359317864, 2640574482158325235170602432759848066882, 1281108882937310168117828239892171279567, 834680326527526516654150386101753621117, 36798432129568720840085214397181578972, 2245967311937524535079578658598265247, 381680204344614899874381912886590172, 308432361542795403340598363090296043, 88653018620081684679364695, 88426842955186189606730010, 88426842955186189606730010], ![0, 0, 0, 0, 0, 0, 149479883330548052947141063271259739933880, 1281108882937310168117828239892171279567, 834680326527526516654150386101753621117, 36798432129568720840085214397181578972, 2245967311937524535079578658598265247, 381680204344614899874381912886590172, 308432361542795403340598363090296043, 88653018620081684679364695, 88426842955186189606730010, 88426842955186189606730010], ![0, 0, 0, 0, 0, 0, 0, 50178949118596367483700538380313270636330, 50144862213888566699698393390163927265472, 3222896271354190284984409718804963114628, 3209049832679700836601592082891121641822, 190970194688288962788081683237256835356, 27582128257828740919311336168015072411, 27273699996417467078276121316324066904, 88426842955186189606730010, 88426842955186189606730010], ![0, 0, 0, 0, 0, 0, 0, 0, 50144862213888566699698393390163927265472, 3738437090789645055487717359011495661506, 3209049832679700836601592082891121641822, 190970194688288962788081683237256835356, 27582128257828740919311336168015072411, 27273699996417467078276121316324066904, 7819306555021164656057160367, 7819306555021164656057160367], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 48826488572907774063518247124420633493712, 3209049832679700836601592082891121641822, 190970194688288962788081683237256835356, 27582128257828740919311336168015072411, 27273699996417467078276121316324066904, 7819306555021164656057160367, 7819306555021164656057160367], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48796696909886697160437141013049591112640, 190970194688288962788081683237256835356, 38821788192823495836666514065129237452, 27273699996417467078276121316324066904, 691436592759314658948885181373, 691436592759314658948885181373], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46765198516624733240057252240137380313705, 1033510416504688798321550338366905996092, 1021161343937896942652655436392719123959, 61141555001396967929927587930696, 61141555001396967929927587930696], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46173208736845139480166346936982994487655, 1091994907060554479345433238669191238698, 5406554682144409393289170560210668, 5406554682144409393289170560210668], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1098234652579264556162997585536328814981, 478084561806610350930381488123374069, 478084561806610350930381488123374069], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 552239081625102758537747250516334240798, 42275508466172149865721348059078428275], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 552166509606722336232106891260156020366]]
def VY : Fin N → Fin N → ℕ := ![![48274174720500258810918489804383078891996, 3186123238382127484788687800574541409813, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![0, 48280592034972520922609011214145131684792, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 96561184069945049572215596556288262202844, 96561184069945049572215596556288262202844, 90298068385748679897506182418360252253646, 2411726823828384917219842577556001127951, 2411726823828384917219842577556001127951, 2411726823828384917219842577556001127951, 2349503296612711918330748403351585975345, 2349503296612711918330748403351585975345, 1552371700084696197860607543863715623884, 1551131797992632857019152452180572606374, 1506682894921806350405208763119663811951, 362561665834951234001118315744466, 362561665834951234001118315744466, 362561665834951234001118315744466], ![0, 0, 0, 4081852843057455610150121058013752248910058, 90298068385748679897506182418360252253646, 2411726823828384917219842577556001127951, 2411726823828384917219842577556001127951, 2411726823828384917219842577556001127951, 2349503296612711918330748403351585975345, 2349503296612711918330748403351585975345, 1552371700084696197860607543863715623884, 1551131797992632857019152452180572606374, 1506682894921806350405208763119663811951, 362561665834951234001118315744466, 362561665834951234001118315744466, 362561665834951234001118315744466], ![0, 0, 0, 0, 4089119796045965733808610803002768092040380, 15374332637501459343234724058523118887433, 15374332637501459343234724058523118887433, 15374332637501459343234724058523118887433, 2381615559722469297402032377215846660474, 2381615559722469297402032377215846660474, 1583938805532027204466435295946158090650, 1561518876239236218167226434855299815901, 1506698562451883383727240763645549324365, 16030091743178957757283007541274648, 16030091743178957757283007541274648, 16030091743178957757283007541274648], ![0, 0, 0, 0, 0, 4268165403941862112612058193941967827930272, 281738819236285731865364689849886816923365, 281738819236285731865364689849886816923365, 4825045727987618611296641757198733405894, 4825045727987618611296641757198733405894, 2073930693378574195226109797813896713360, 2020074429566235092250101747328188796955, 1965254115778882180540140334838458317086, 16030091743178957757283007541274648, 16030091743178957757283007541274648, 16030091743178957757283007541274648], ![0, 0, 0, 0, 0, 0, 4268732866800895099966427956539256328412723, 281738819236285731865364689849886816923365, 4825045727987618611296641757198733405894, 4825045727987618611296641757198733405894, 2073930693378574195226109797813896713360, 2020074429566235092250101747328188796955, 1965254115778882180540140334838458317086, 16030091743178957757283007541274648, 16030091743178957757283007541274648, 16030091743178957757283007541274648], ![0, 0, 0, 0, 0, 0, 0, 4269300329659927700970919012736644887232157, 3992386556151630130538430547135816221751223, 106630694550741330715959632132114697334649, 103879579516132283209090070521530661108811, 68635664265732417437949617138095375321297, 68580843951945071094187593734403943849699, 66615605866257938305723624839233061710610, 16030091743178957757283007541274648, 16030091743178957757283007541274648], ![0, 0, 0, 0, 0, 0, 0, 0, 4565507710439456088607290800328380926569932, 679751848838568042167083362804484288396238, 105299372539603356095605061635625680198809, 70031354003702906849907609289421507797420, 69040092220382900314840727724314706463333, 66616298581368746050825979192276788755904, 708745202565656811511074759336776866, 708745202565656811511074759336776866], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 12456637161493317676961674393853814275876985, 213331780420176707424011863683535629499151, 91695571861663795129403343059300148786808, 89314402170520422028190013604603491137160, 86890608531506294808666774520558569346142, 708745202565656811511074759336776866, 708745202565656811511074759336776866], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25552978932672513734248593580835393081313589, 154469479219336937417599460931377449587270, 151022620807360603154527541815891517225405, 107195545786802512785975526505145324014552, 31336050361257477129212249528217602418, 31336050361257477129212249528217602418], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82206733886238051594990443724839707940490799, 1989106844185668524480867331933543828521155, 1939130414016093034033182088759656070802976, 1385474002065360454230506906756948475832, 1385474002065360454230506906756948475832], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124665598284576374623344829291320721315615819, 2270885517032493221613073851267245674327976, 61256545999563484562571979505605520099971, 61256545999563484562571979505605520099971], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 664449300490378753626092150207257031673672543, 2708361486540270935158842482174931996240319, 2708361486540270935158842482174931996240319], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1354988458570874941787198124308360874369473275, 119745927918085569541989044791756341870498870], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3863498787063998999416630152243568915351827413]]

def P1Z : Fin N → Fin N → ℕ := ![![4201879520421705768344135288555111289541366800, 36011970699367788825792151823368934668628370, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1410530259723743889966822133870606037587236300, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 705265129861871944983411066935303018793618150, 2458768506811222006701326380635350261180170, 2156229075197208368087030915777048872415296, 119247162040105040544423159595783635241236, 96686888140625708549532291564148893438840, 74126614241146376554641423532514151636444, 73808146151633119241836617906495797761906, 3253969178918451327303183656063086946762, 198603798775181260785569321494988638796, 33750775488684648986123303429820993271, 27273699996441990591574031496721373024, 108426842955186189606730010, 88426842955186189606730030, 88426842955186189606730030], ![0, 0, 0, 121999177737289197633887058737261407103680566, 2156229075197208368087030915777048872415296, 119247162040105040544423159595783635241236, 96686888140625708549532291564148893438840, 74126614241146376554641423532514151636444, 73808146151633119241836617906495797761906, 3253969178918451327303183656063086946762, 198603798775181260785569321494988638796, 33750775488684648986123303429820993271, 27273699996441990591574031496721373024, 108426842955186189606730010, 88426842955186189606730030, 88426842955186189606730030], ![0, 0, 0, 0, 88338136129314453543187373415866155736722969, 121824866137282314396939697796816297975626, 98233510598932072861042214484768491079474, 74126614241146376554641423532514151636444, 73808146151633119241836617906495797761906, 3253969178918451327303183656063086946762, 198603798775181260785569321494988638796, 33750775488684648986123303429820993271, 27273699996441990591574031496721373024, 7839306555021164656057160367, 7819306555021164656057160387, 7819306555021164656057160387], ![0, 0, 0, 0, 0, 26365164618490056659810741799651926253298188, 233497665045286459885133803780995904576092, 113284413999991579763206441500519895786272, 73808146151633119241836617906495797761906, 3253969178918451327303183656063086946762, 198603798775181260785569321494988638796, 33750775488684648986123303429820993271, 27273699996441990591574031496721373024, 7839306555021164656057160367, 7819306555021164656057160387, 7819306555021164656057160387], ![0, 0, 0, 0, 0, 0, 13218034168229924423040199406732817720910002, 113284413999991579763206441500519895786272, 73808146151633119241836617906495797761906, 3253969178918451327303183656063086946762, 198603798775181260785569321494988638796, 33750775488684648986123303429820993271, 27273699996441990591574031496721373024, 7839306555021164656057160367, 7819306555021164656057160387, 7819306555021164656057160387], ![0, 0, 0, 0, 0, 0, 0, 4437166053366398647101582429526053883744738, 4434151855996974300075439332833106859535586, 284990542447892245668132793927291305604880, 283766145589734514640712404853559850933588, 16886891414822655839625436191067383836615, 2439000523824825681635751713543702635669, 2411727186390069752171076578674316872417, 7819306555021164656057160388, 7819306555021164656057160388], ![0, 0, 0, 0, 0, 0, 0, 0, 4434151855996974300075439332833106859535586, 330578189525099241991968342857449775075698, 283766145589734514640712404853559850933588, 16886891414822655839625436191067383836615, 2439000523824825681635751713543702635669, 2411727186390069752171076578674316872417, 691436592759314658948885181394, 691436592759314658948885181394], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4317572237089708610093031609546819286565056, 283766145589734514640712404853559850933588, 16886891414822655839625436191067383836615, 2439000523824825681635751713543702635669, 2411727186390069752171076578674316872417, 691436592759314658948885181394, 691436592759314658948885181394], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4314937854382369393535213059438450053457245, 16886891414822655839625436191067383836615, 3432888167766305157210131028620097692724, 2411727186390069752171076578674316872417, 61141555001396967929927587930717, 61141555001396967929927587930717], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4135298864997680186401440621308649802152852, 91390063292809257674189248671700820933158, 90298073792303381041915575707530812464314, 5406554682144409393289170560210689, 5406554682144409393289170560210689], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4082951077710034898003621688613959955165853, 96561662154506875182566526937776385576913, 478084561806610350930381488123374090, 478084561806610350930381488123374090], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 97113423151570171330753343806804596443642, 42275508466172149865721348059078428296, 42275508466172149865721348059078428296], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48832758544579243258841118105405287705177, 3738289747988849821020794691834697430198], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48826341230106981147150596695643234912381]]
def P1Y : Fin N → Fin N → ℕ := ![![4268732866800895099966427956539256328412723, 281738819236285731865364689849886816923365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 4269300329659927700970919012736644887232157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 8538600659319855401941838025473289774464314, 8538600659319855401941838025473289774464314, 7984773112303260261076861094271632443502446, 213261389101482661431919264264229394669298, 213261389101482661431919264264229394669298, 213261389101482661431919264264229394669298, 207759159032264566418180141043061322217622, 207759159032264566418180141043061322217622, 137271328531464834875899234276190750642594, 137161687903890142188375187468807887699398, 133231211732515876611447249678466123421220, 32060183486357915514566015082549296, 32060183486357915514566015082549296, 32060183486357915514566015082549296], ![0, 0, 0, 360945360319222144239970719070413389453409904, 7984773112303260261076861094271632443502446, 213261389101482661431919264264229394669298, 213261389101482661431919264264229394669298, 213261389101482661431919264264229394669298, 207759159032264566418180141043061322217622, 207759159032264566418180141043061322217622, 137271328531464834875899234276190750642594, 137161687903890142188375187468807887699398, 133231211732515876611447249678466123421220, 32060183486357915514566015082549296, 32060183486357915514566015082549296, 32060183486357915514566015082549296], ![0, 0, 0, 0, 361587954029899797382727163183977174802721784, 1359503697677136084334166725608968576792476, 1359503697677136084334166725608968576792476, 1359503697677136084334166725608968576792476, 210598745079206712191210123271251360397618, 210598745079206712191210123271251360397618, 140062708007405813699815218578843015594840, 138080184440765800629681455448629412926666, 133232597162737492101651958384553577511808, 1417490405131313623022149518673553732, 1417490405131313623022149518673553732, 1417490405131313623022149518673553732], ![0, 0, 0, 0, 0, 377420391881126116926919630909408354771972220, 24913274322986635353923348787707628551753970, 24913274322986635353923348787707628551753970, 426663560840353414848023727367071258998302, 426663560840353414848023727367071258998302, 183391143723327590258806686118600297573616, 178628804341040844056380027209206982274320, 173781217063012589617333549041117138692284, 1417490405131313623022149518673553732, 1417490405131313623022149518673553732, 1417490405131313623022149518673553732], ![0, 0, 0, 0, 0, 0, 377470570830244713294403331447788668042608550, 24913274322986635353923348787707628551753970, 426663560840353414848023727367071258998302, 426663560840353414848023727367071258998302, 183391143723327590258806686118600297573616, 178628804341040844056380027209206982274320, 173781217063012589617333549041117138692284, 1417490405131313623022149518673553732, 1417490405131313623022149518673553732, 1417490405131313623022149518673553732], ![0, 0, 0, 0, 0, 0, 0, 377520749779363309661887031986168981313244880, 353034139017217027722811706925828424020489212, 9429015681240831966212002769089358840515611, 9185743264123806141622785727840887879090925, 6069235105150806326555223165704737773071772, 6064387517872778072116176687536647929489736, 5890607718300170613812466160645049464351184, 1417490405131313623022149518673560759, 1417490405131313623022149518673560759], ![0, 0, 0, 0, 0, 0, 0, 0, 403713433321721701776460870360132138924118088, 60108309985745506019861166203393073744144487, 9311291078839152426199177963585042480691849, 6192651542424486688807898222127313825248262, 6104997392383370508070794191505821438826556, 5890668972910487997453101562994587226002288, 62672100722514954258424499056435211863, 62672100722514954258424499056435211863], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1101501098029106195528057438768812978678001938, 18864255844565225302379022216866207265154354, 8108349932697333937872656928823550930362289, 7897790614368951484149611516474380607114438, 7683462194896068973531918887963146394290170, 62672100722514954258424499056435211863, 62672100722514954258424499056435211863], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2259569255116615029676819526507085649807611926, 13659248380297709900856473357102458146500047, 13354453572813112959746722431977541890963177, 9478963692785057612588819268271743646308889, 2770948004130720908461013813513896958691, 2770948004130720908461013813513896958691], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7269281947217160320902527585612712914055062457, 175890438531892079017478250401396230867019855, 171471180589826219543377246657872950558563845, 122513091999126969125143959011211040206969, 122513091999126969125143959011211040206969], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11023785281424568528953420122965125937538243328, 200807236983839010663665232978169822079289156, 5416722973080541870317684964349863992487665, 5416722973080541870317684964349863992487665], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58755153946146041091427491160136043473801704646, 239491855836171139083978089583512683741004767, 239491855836171139083978089583512683741004767], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 119817351632136580414539450127525781280829171018, 10588754362535605125020631896011433339624568911], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 341637000501260545168462699851867595488148991828]]

def P2Z : Fin N → Fin N → ℕ := ![![371558940468943175531660005323259506134780156220, 3184424877539763307143733070579614270552105920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 124728737760129465970025482093977374672064585180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 62364368880064732985012741046988687336032292590, 217421136614953533707977539046776640303492162, 190668529807869894903243891311823594960030198, 10544650070572013089720913375309778307380560, 8549716273436767370043983817818739168146400, 6554782476301521650367054260327700028912240, 6526621348563893836736385311631876571472524, 287738221565238139856423791283459623709508, 17561906924596348819347902259663803702035, 2984474523753665493467232343478130096149, 2411727186392238289030180302466451472617, 9587843414124888448191760988, 7819306555021164656057160388, 7819306555021164656057160388], ![0, 0, 0, 10788002130437126204240814434659508117074348802, 190668529807869894903243891311823594960030198, 10544650070572013089720913375309778307380560, 8549716273436767370043983817818739168146400, 6554782476301521650367054260327700028912240, 6526621348563893836736385311631876571472524, 287738221565238139856423791283459623709508, 17561906924596348819347902259663803702035, 2984474523753665493467232343478130096149, 2411727186392238289030180302466451472617, 9587843414124888448191760988, 7819306555021164656057160388, 7819306555021164656057160388], ![0, 0, 0, 0, 7811462490460753091633741344298786194446497904, 10772588305958048071340091119960570654734650, 8686479214668388359015490464609214576558854, 6554782476301521650367054260327700028912240, 6526621348563893836736385311631876571472524, 287738221565238139856423791283459623709508, 17561906924596348819347902259663803702035, 2984474523753665493467232343478130096149, 2411727186392238289030180302466451472617, 693205129618418382741019781994, 691436592759314658948885181394, 691436592759314658948885181394], ![0, 0, 0, 0, 0, 2331388271206853186121310723525077945313128866, 20647461357362216463318680264677323111026928, 10017383086047553523455687488092645398662656, 6526621348563893836736385311631876571472524, 287738221565238139856423791283459623709508, 17561906924596348819347902259663803702035, 2984474523753665493467232343478130096149, 2411727186392238289030180302466451472617, 693205129618418382741019781994, 691436592759314658948885181394, 691436592759314658948885181394], ![0, 0, 0, 0, 0, 0, 1168829031570353407763004822495739177018218113, 10017383086047553523455687488092645398662656, 6526621348563893836736385311631876571472524, 287738221565238139856423791283459623709508, 17561906924596348819347902259663803702035, 2984474523753665493467232343478130096149, 2411727186392238289030180302466451472617, 693205129618418382741019781994, 691436592759314658948885181394, 691436592759314658948885181394], ![0, 0, 0, 0, 0, 0, 0, 392364585767114094295793557839876874960253211, 392098049809692071581683353406227506360073977, 25200813940753098312518987009669593186824682, 25092544392061961206310465157682002132900439, 1493254495139805974257058590591959860391740, 215673116287874791294106489380506239411905, 213261421161667827899850927367847005089164, 691436592759314658948885181394, 691436592759314658948885181394], ![0, 0, 0, 0, 0, 0, 0, 0, 392098049809692071581683353406227506360073977, 29231985649545733191413487664254483389348339, 25092544392061961206310465157682002132900439, 1493254495139805974257058590591959860391740, 215673116287874791294106489380506239411905, 213261421161667827899850927367847005089164, 61141555001396967929927587930717, 61141555001396967929927587930717], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 381789282156803811131893470324335522880202919, 25092544392061961206310465157682002132900439, 1493254495139805974257058590591959860391740, 215673116287874791294106489380506239411905, 213261421161667827899850927367847005089164, 61141555001396967929927587930717, 61141555001396967929927587930717], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 381556332010858082121651807873482171172997221, 1493254495139805974257058590591959860391740, 303559462893788102583850988509362735003802, 213261421161667827899850927367847005089164, 5406554682144409393289170560210689, 5406554682144409393289170560210689], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 365671423307909764678552024779189572463975093, 8081334774457769196369443769747011356949549, 7984773590387823747797228173190723094747106, 478084561806610350930381488123374090, 478084561806610350930381488123374090], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 361042473742373716471411488562757796577723736, 8538642934828323254201719895358951380763180, 42275508466172149865721348059078428296, 42275508466172149865721348059078428296], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8587433417864436325310695292116297590040061, 3738289747988849821020794691834697430198, 3738289747988849821020794691834697430198], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4318126670890034682118069609432288122144538, 330565160466392713012515286545530051835746], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4317559208031002081113578553234899563325104]]
def P2Y : Fin N → Fin N → ℕ := ![![377470570830244713294403331447788668042608550, 24913274322986635353923348787707628551753970, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 377520749779363309661887031986168981313244880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 755041499558726619323774063972337962626489760, 755041499558726619323774063972337962626489760, 706068278034434055445623413851656848040978424, 18858031362481663932424005538178717681031222, 18858031362481663932424005538178717681031222, 18858031362481663932424005538178717681031222, 18371486528247612283245571455681775758181850, 18371486528247612283245571455681775758181850, 12138470210301612653110446331409475546143544, 12128775035745556144232353375073295858979472, 11781215436600341227624932321290098928702368, 2834980810262627246044299037347121518, 2834980810262627246044299037347121518, 2834980810262627246044299037347121518], ![0, 0, 0, 31917258692350944317918187466533814388165784734, 706068278034434055445623413851656848040978424, 18858031362481663932424005538178717681031222, 18858031362481663932424005538178717681031222, 18858031362481663932424005538178717681031222, 18371486528247612283245571455681775758181850, 18371486528247612283245571455681775758181850, 12138470210301612653110446331409475546143544, 12128775035745556144232353375073295858979472, 11781215436600341227624932321290098928702368, 2834980810262627246044299037347121518, 2834980810262627246044299037347121518, 2834980810262627246044299037347121518], ![0, 0, 0, 0, 31974081225489027500794436725711266757271275888, 120216619971491012039722332406786147488288974, 120216619971491012039722332406786147488288974, 120216619971491012039722332406786147488288974, 18622582157678304852398355927170084961383698, 18622582157678304852398355927170084961383698, 12385303084848973377615796444254627650496524, 12209994784766741016141588383011642877653112, 11781337945820975994906203125989174452004576, 125344201445029908516848998112870423726, 125344201445029908516848998112870423726, 125344201445029908516848998112870423726], ![0, 0, 0, 0, 0, 33374093720957162886944731444958154490662788326, 2203002196058212391056114877537625957356003876, 2203002196058212391056114877537625957356003876, 37728511689130450604758044433732414530308708, 37728511689130450604758044433732414530308708, 16216699865394667875745313857647101860724578, 15795581228737902968299223032948761214228876, 15366924389792137947063837775926292788580340, 125344201445029908516848998112870423726, 125344201445029908516848998112870423726, 125344201445029908516848998112870423726], ![0, 0, 0, 0, 0, 0, 33378530887010529285591833027387680544546533064, 2203002196058212391056114877537625957356003876, 37728511689130450604758044433732414530308708, 37728511689130450604758044433732414530308708, 16216699865394667875745313857647101860724578, 15795581228737902968299223032948761214228876, 15366924389792137947063837775926292788580340, 125344201445029908516848998112870423726, 125344201445029908516848998112870423726, 125344201445029908516848998112870423726], ![0, 0, 0, 0, 0, 0, 0, 33382968053063895684238934609817206598430277802, 31217694368694813743787577776713313055604582634, 833778088867071281600809708857885722220442052, 812266277043335498871796978281800409550857922, 536683299501273491017764506195925704763520864, 536254642662327725996529120938903236337872328, 520887843616737033079373800011975056419715714, 125344201445029908516848998112870423726, 125344201445029908516848998112870423726], ![0, 0, 0, 0, 0, 0, 0, 0, 35699104367238913352536458785293751940689497778, 5315188087411170890349690717438324607305357196, 823368073938536250797764611138358223983133438, 547596625418161813968958728026932027331218342, 539845645658105703274642921699520430841909766, 520893260168543849491282205190603971343209370, 5541896008261441816922027627027793917382, 5541896008261441816922027627027793917382], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 97402264610384908980057120284125681424449807906, 1668106589033823373414548185883263137749198578, 716995786124321901914037086048423270597390152, 698376690349746969202741051357817761487346458, 679424304860185115419380334848901301988646062, 5541896008261441816922027627027793917382, 5541896008261441816922027627027793917382], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 199806575668563948790295137797379511610036491990, 1207844211410466981302251757221020587608763612, 1180892168835470558992416035795317505957293062, 838194833839816373843911830397594026920579310, 245026183998253938250287918022422080413938, 245026183998253938250287918022422080413938], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 642799653143541802105884513239221728237028789819, 15553436185378461223874896711121662070620863304, 15162655157356944286288201615094022154447260322, 10833445946161083740635369928699727984975330, 10833445946161083740635369928699727984975330], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 974798529852223273956179344067007994665166746574, 17756750009034799319258176655891631652795064124, 478983711672342278167956179167025367482009534, 478983711672342278167956179167025367482009534], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5195532770803647318227508467609425875624413082086, 21177508725071210250041263792022866679249137822, 21177508725071210250041263792022866679249137822], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10595070136081269405133784534412483817101807463756, 936330119106978542415766850566548694892749539646], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30209881391005847524491164072380502222583482487256]]

def P3Z : Fin N → Fin N → ℕ := ![![32855784077442634292218065560355228265982111156430, 281588638548796729544339375290284262156407260160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 11029368505913577190654756910878938955132717761210, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 5514684252956788595327378455439469477566358880605, 19225864702588590620493884334153966873052407339, 16860216141816759078012384196467782773483181011, 932430115807864637563202519357774947912513234, 756024418222592949375569610290087795604740460, 579618720637321261187936701222400643296967686, 577128521017425107745140698626686049056710097, 25443782530553888182697423202875278206941139, 1552943985614879284126403237461522462314720, 263907660015719557074710095429835268864245, 213261421161859584768133425136810840308924, 847822723859737952070028389154, 691436592759314658948885181394, 691436592759314658948885181394], ![0, 0, 0, 953948970188377669779184053409035751629100185795, 16860216141816759078012384196467782773483181011, 932430115807864637563202519357774947912513234, 756024418222592949375569610290087795604740460, 579618720637321261187936701222400643296967686, 577128521017425107745140698626686049056710097, 25443782530553888182697423202875278206941139, 1552943985614879284126403237461522462314720, 263907660015719557074710095429835268864245, 213261421161859584768133425136810840308924, 847822723859737952070028389154, 691436592759314658948885181394, 691436592759314658948885181394], ![0, 0, 0, 0, 690742966894300508946868678945163716307530450906, 952585974351827811957675022630699398925131519, 768117933348970854012253112253842466212311431, 579618720637321261187936701222400643296967686, 577128521017425107745140698626686049056710097, 25443782530553888182697423202875278206941139, 1552943985614879284126403237461522462314720, 263907660015719557074710095429835268864245, 213261421161859584768133425136810840308924, 61297941132497391223048731138477, 61141555001396967929927587930717, 61141555001396967929927587930717], ![0, 0, 0, 0, 0, 206157304525571407137664111470379320092256358312, 1825789822870745087833693060234085584684875171, 885805560971865777382273210517727386616696559, 577128521017425107745140698626686049056710097, 25443782530553888182697423202875278206941139, 1552943985614879284126403237461522462314720, 263907660015719557074710095429835268864245, 213261421161859584768133425136810840308924, 61297941132497391223048731138477, 61141555001396967929927587930717, 61141555001396967929927587930717], ![0, 0, 0, 0, 0, 0, 103355861216133987650269764592296025571183250658, 885805560971865777382273210517727386616696559, 577128521017425107745140698626686049056710097, 25443782530553888182697423202875278206941139, 1552943985614879284126403237461522462314720, 263907660015719557074710095429835268864245, 213261421161859584768133425136810840308924, 61297941132497391223048731138477, 61141555001396967929927587930717, 61141555001396967929927587930717], ![0, 0, 0, 0, 0, 0, 0, 34695561606805275833777605071858814591200388812, 34671992673556408446030630426094965048506244065, 2228428416681841682889992952838241571759242980, 2218854482302901613668789977985100803042059583, 132043780733853440562120108958522184518273273, 19071292783643513929348724838427080329579158, 18858034197462622761875796984606220114200112, 61141555001396967929927587930717, 61141555001396967929927587930717], ![0, 0, 0, 0, 0, 0, 0, 0, 34671992673556408446030630426094965048506244065, 2584892204300637803805334295554041740799339762, 2218854482302901613668789977985100803042059583, 132043780733853440562120108958522184518273273, 19071292783643513929348724838427080329579158, 18858034197462622761875796984606220114200112, 5406554682144409393289170560210689, 5406554682144409393289170560210689], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 33760420895252954698341052445404096327989868950, 2218854482302901613668789977985100803042059583, 132043780733853440562120108958522184518273273, 19071292783643513929348724838427080329579158, 18858034197462622761875796984606220114200112, 5406554682144409393289170560210689, 5406554682144409393289170560210689], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33739821849281023971267659347151870147598590250, 132043780733853440562120108958522184518273273, 26842804952869669849246102084249956419237100, 18858034197462622761875796984606220114200112, 478084561806610350930381488123374090, 478084561806610350930381488123374090], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32335169522047942669793339787699771416426979347, 714606920969262560868850002119896315065200376, 706068320309942670184597824975133372205454092, 42275508466172149865721348059078428296, 42275508466172149865721348059078428296], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31925846125768808936412523030198811201399283567, 755045237848474756740419630169158262409967330, 3738289747988849821020794691834697430198, 3738289747988849821020794691834697430198], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759359626229616802572716678983898715834681670, 330565160466392713012515286545530051835746, 330565160466392713012515286545530051835746], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 381838308987394311743000610539403880876569984, 29230833531017637435036927340942528115079074], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 381788130038275715375516910001023567605933654]]
def P3Y : Fin N → Fin N → ℕ := ![![33378530887010529285591833027387680544546533064, 2203002196058212391056114877537625957356003876, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 33382968053063895684238934609817206598430277802, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 66765936106127791368477869219634413196860555604, 66765936106127791368477869219634413196860555604, 62435388737389627487575155553426626111209165268, 1667556177734142563201619417715771444440884104, 1667556177734142563201619417715771444440884104, 1667556177734142563201619417715771444440884104, 1624532554086670997743593956563600819101715844, 1624532554086670997743593956563600819101715844, 1073366599002546982035529012391851409527041728, 1072509285324655451993058241877806472675744656, 1041775687233474066158747600023950112839431428, 250688402890059817033697996225740847452, 250688402890059817033697996225740847452, 250688402890059817033697996225740847452], ![0, 0, 0, 2822342421948570075607836025929089706042718856457, 62435388737389627487575155553426626111209165268, 1667556177734142563201619417715771444440884104, 1667556177734142563201619417715771444440884104, 1667556177734142563201619417715771444440884104, 1624532554086670997743593956563600819101715844, 1624532554086670997743593956563600819101715844, 1073366599002546982035529012391851409527041728, 1072509285324655451993058241877806472675744656, 1041775687233474066158747600023950112839431428, 250688402890059817033697996225740847452, 250688402890059817033697996225740847452, 250688402890059817033697996225740847452], ![0, 0, 0, 0, 2827367059162687225038726867837882673602197549620, 10630376174822341780699381434876649214610714392, 10630376174822341780699381434876649214610714392, 10630376174822341780699381434876649214610714392, 1646736147877072501595529222276716447966266876, 1646736147877072501595529222276716447966266876, 1095193250836323627937917456053864054662436684, 1079691291316211406549285843399040861683819532, 1041786520337087698982564410381207942686418740, 11083792016522883633844055254055587834764, 11083792016522883633844055254055587834764, 11083792016522883633844055254055587834764], ![0, 0, 0, 0, 0, 2951165744234746330388063984393386409444678423087, 194804529220769817960114240568251362848899615812, 194804529220769817960114240568251362848899615812, 3336213178067646746829096371766526275498397156, 3336213178067646746829096371766526275498397156, 1433991572248643803828074172096846541194780304, 1396753380699493938405482102715635522974692916, 1358848609720370230838760669697802603977292124, 11083792016522883633844055254055587834764, 11083792016522883633844055254055587834764, 11083792016522883633844055254055587834764], ![0, 0, 0, 0, 0, 0, 2951558108820513444482359777951226286319638676298, 194804529220769817960114240568251362848899615812, 3336213178067646746829096371766526275498397156, 3336213178067646746829096371766526275498397156, 1433991572248643803828074172096846541194780304, 1396753380699493938405482102715635522974692916, 1358848609720370230838760669697802603977292124, 11083792016522883633844055254055587834764, 11083792016522883633844055254055587834764, 11083792016522883633844055254055587834764], ![0, 0, 0, 0, 0, 0, 0, 2951950473406280558576655571509066163194598929509, 2760482157363578387363370427312581326621197710853, 73728364123723805356152212350593545491900880868, 71826142517904802413151190150923865757597264016, 47457209841670286575534772390038383626141003396, 47419305070691162867968050957020550707143602604, 46060467544762809160012924131378002158754145244, 11083792016522883633844055254055587834764, 11083792016522883633844055254055587834764], ![0, 0, 0, 0, 0, 0, 0, 0, 3156759095522638638197131606535573823565772297677, 470005302282784056189913391573586042436475467692, 72807839368477092571927619493269060391620010936, 48422240798641733755114122358913383115080896604, 47736846128650425384817113948117936157007469100, 46060946513338789145005790863158792947327138356, 490052367996507876500575836044844160827876, 490052367996507876500575836044844160827876], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 8612974756182001293931225163272318220127091664031, 147505399381005229050344869734329590676403750280, 63401673779145706116786683566399585841393653182, 61755245921119797056986897948607468188405911420, 60079346305808160817175574863648324978725580676, 490052367996507876500575836044844160827876, 490052367996507876500575836044844160827876], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17668264688057640943086219480689166178189414121020, 106805850396724126245056613722206254132062112158, 104422566360623424554045261518489856474857715764, 74118922937801858148950129028159211621933145780, 21666891892322167481270739857399455969950660, 21666891892322167481270739857399455969950660], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56840743980172158522822659114521586577705874264556, 1375341258977971350123611177559967665089722329594, 1340785726383246436041430736606518452519096220414, 957967423344684556335912358334050734964019068, 957967423344684556335912358334050734964019068], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 86198356512188980473655219967571215289930275195826, 1570173344443420901866040694465745184771137698018, 42355017450142420500082527584045733358498275644, 42355017450142420500082527584045733358498275644], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 459424560392377417495952100406014473544502534957442, 1872660238213957084831533701133097389785499079292, 1872660238213957084831533701133097389785499079292], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 936888603022441452420351390819140016265764805034372, 82796716396483611808281340431723953924336613274352], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2671364437457275389509957185551305554054267122732452]]

def witnessZ0 : Fin N → Fin N → Fin N × Fin N := ![![(0, 0), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2)], ![(1, 0), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2)], ![(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 14)], ![(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 14)], ![(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 14)], ![(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 14)], ![(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 14)], ![(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 14)], ![(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 14)], ![(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 14)], ![(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 14)], ![(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 14)], ![(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 14)], ![(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 14)], ![(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], ![(15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)]]
def witnessY0 : Fin N → Fin N → Fin N × Fin N := ![![(0, 0), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2)], ![(1, 0), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2)], ![(2, 0), (2, 1), (2, 2), (2, 2), (2, 4), (2, 5), (2, 5), (2, 5), (2, 8), (2, 8), (2, 10), (2, 11), (2, 12), (2, 13), (2, 13), (2, 13)], ![(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 5), (3, 5), (3, 8), (3, 8), (3, 10), (3, 11), (3, 12), (3, 13), (3, 13), (3, 13)], ![(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 5), (4, 5), (4, 8), (4, 8), (4, 10), (4, 11), (4, 12), (4, 13), (4, 13), (4, 13)], ![(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 6), (5, 8), (5, 8), (5, 10), (5, 11), (5, 12), (5, 13), (5, 13), (5, 13)], ![(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 8), (6, 10), (6, 11), (6, 12), (6, 13), (6, 13), (6, 13)], ![(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 14)], ![(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 14)], ![(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 14)], ![(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 14)], ![(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 14)], ![(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 14)], ![(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 14)], ![(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], ![(15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)]]

def witnessZ1 : Fin N → Fin N → Fin N × Fin N := ![![(0, 0), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2)], ![(1, 0), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2)], ![(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 14)], ![(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 14)], ![(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 14)], ![(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 14)], ![(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 14)], ![(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 14)], ![(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 14)], ![(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 14)], ![(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 14)], ![(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 14)], ![(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 14)], ![(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 14)], ![(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], ![(15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)]]
def witnessY1 : Fin N → Fin N → Fin N × Fin N := ![![(0, 0), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2)], ![(1, 0), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2)], ![(2, 0), (2, 1), (2, 2), (2, 2), (2, 4), (2, 5), (2, 5), (2, 5), (2, 8), (2, 8), (2, 10), (2, 11), (2, 12), (2, 13), (2, 13), (2, 13)], ![(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 5), (3, 5), (3, 8), (3, 8), (3, 10), (3, 11), (3, 12), (3, 13), (3, 13), (3, 13)], ![(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 5), (4, 5), (4, 8), (4, 8), (4, 10), (4, 11), (4, 12), (4, 13), (4, 13), (4, 13)], ![(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 6), (5, 8), (5, 8), (5, 10), (5, 11), (5, 12), (5, 13), (5, 13), (5, 13)], ![(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 8), (6, 10), (6, 11), (6, 12), (6, 13), (6, 13), (6, 13)], ![(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 14)], ![(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 14)], ![(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 14)], ![(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 14)], ![(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 14)], ![(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 14)], ![(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 14)], ![(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], ![(15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)]]

def witnessZ2 : Fin N → Fin N → Fin N × Fin N := ![![(0, 0), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2)], ![(1, 0), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2)], ![(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 14)], ![(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 14)], ![(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 14)], ![(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 14)], ![(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 14)], ![(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 14)], ![(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 14)], ![(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 14)], ![(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 14)], ![(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 14)], ![(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 14)], ![(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 14)], ![(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], ![(15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)]]
def witnessY2 : Fin N → Fin N → Fin N × Fin N := ![![(0, 0), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2)], ![(1, 0), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2)], ![(2, 0), (2, 1), (2, 2), (2, 2), (2, 4), (2, 5), (2, 5), (2, 5), (2, 8), (2, 8), (2, 10), (2, 11), (2, 12), (2, 13), (2, 13), (2, 13)], ![(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 5), (3, 5), (3, 8), (3, 8), (3, 10), (3, 11), (3, 12), (3, 13), (3, 13), (3, 13)], ![(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 5), (4, 5), (4, 8), (4, 8), (4, 10), (4, 11), (4, 12), (4, 13), (4, 13), (4, 13)], ![(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 6), (5, 8), (5, 8), (5, 10), (5, 11), (5, 12), (5, 13), (5, 13), (5, 13)], ![(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 8), (6, 10), (6, 11), (6, 12), (6, 13), (6, 13), (6, 13)], ![(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 14)], ![(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 14)], ![(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 14)], ![(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 14)], ![(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 14)], ![(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 14)], ![(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 14)], ![(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], ![(15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)]]

def witnessZ3 : Fin N → Fin N → Fin N × Fin N := ![![(0, 0), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2)], ![(1, 0), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2)], ![(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 14)], ![(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 14)], ![(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 14)], ![(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 14)], ![(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 14)], ![(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 14)], ![(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 14)], ![(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 14)], ![(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 14)], ![(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 14)], ![(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 14)], ![(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 14)], ![(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], ![(15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)]]
def witnessY3 : Fin N → Fin N → Fin N × Fin N := ![![(0, 0), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2)], ![(1, 0), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2)], ![(2, 0), (2, 1), (2, 2), (2, 2), (2, 4), (2, 5), (2, 5), (2, 5), (2, 8), (2, 8), (2, 10), (2, 11), (2, 12), (2, 13), (2, 13), (2, 13)], ![(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 5), (3, 5), (3, 8), (3, 8), (3, 10), (3, 11), (3, 12), (3, 13), (3, 13), (3, 13)], ![(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 5), (4, 5), (4, 8), (4, 8), (4, 10), (4, 11), (4, 12), (4, 13), (4, 13), (4, 13)], ![(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 6), (5, 8), (5, 8), (5, 10), (5, 11), (5, 12), (5, 13), (5, 13), (5, 13)], ![(6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 8), (6, 10), (6, 11), (6, 12), (6, 13), (6, 13), (6, 13)], ![(7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 14)], ![(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 14)], ![(9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 14)], ![(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (10, 14), (10, 14)], ![(11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (11, 14), (11, 14)], ![(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 14), (12, 14)], ![(13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (13, 12), (13, 13), (13, 14), (13, 14)], ![(14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], ![(15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)]]

theorem initial_positive : ∀ i j : Fin N, i ≤ j → 1 ≤ VZ i j ∧ 1 ≤ VY i j := by decide +kernel
theorem final_bounds : VZ output output ≤ C ∧ VY output output ≤ C := by decide +kernel

def periodRecipe0 : SensitivityNQ.Recipe N := ⟨![6, 7, 7, 7, 8, 9, 9, 9, 10, 10, 11, 12, 13, 14, 15, 15], ![14, 14, 14, 7, 7, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0], ![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
theorem period_valid0 : periodRecipe0.Valid := by
  unfold SensitivityNQ.Recipe.Valid Monotone
  decide +kernel
theorem period_tolerance_bound0 : ∀ a : Fin N, 3 ≤ a.val → periodRecipe0.tol a < 5 := by decide +kernel
theorem period_defect0 : ∀ a : Fin N, 3 ≤ a.val → 0 < periodRecipe0.tol a →
    SensitivityQ.DefectBound periodTournament periodLabeling.label (periodRecipe0.tol a) (v (periodRecipe0.tol a)) := by
  intro a ha _
  exact SensitivitySourceLabelsBelow14567.cyclic_defect D (by decide +kernel) (by decide +kernel) (periodRecipe0.tol a) (period_tolerance_bound0 a ha)

theorem compatible0 : SensitivityNQ.Compatible periodRecipe0 VZ VY := by
  unfold SensitivityNQ.Compatible
  decide +kernel
theorem certificateZ0 : ∀ i j : Fin N, i ≤ j →
    let b := witnessZ0 i j
    i ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ j ∧
      SensitivityNQ.rawZeroSourceCombined K t v w periodRecipe0 VZ VY b.1 b.2 ≤ P1Z i j := by decide +kernel
theorem certificateY0 : ∀ i j : Fin N, i ≤ j →
    let b := witnessY0 i j
    i ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ j ∧
      SensitivityNQ.rawOne D periodRecipe0 VZ VY b.1 b.2 ≤ P1Y i j := by decide +kernel
def step0 {I : Type} (F : Fin N → (I → Bool) → Bool) :
    Fin N → (((Fin K × Fin 2) × I) → Bool) → Bool :=
  SensitivityNQ.stage periodTournament periodLabeling.label periodRecipe0 F
theorem step0_nested {I : Type} {F : Fin N → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (step0 F) :=
  SensitivityNQ.stage_nested periodTournament periodLabeling.label periodRecipe0 period_valid0 F hF

def periodRecipe1 : SensitivityNQ.Recipe N := ⟨![6, 7, 7, 7, 8, 9, 9, 9, 10, 10, 11, 12, 13, 14, 15, 15], ![14, 14, 14, 7, 7, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0], ![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
theorem period_valid1 : periodRecipe1.Valid := by
  unfold SensitivityNQ.Recipe.Valid Monotone
  decide +kernel
theorem period_tolerance_bound1 : ∀ a : Fin N, 3 ≤ a.val → periodRecipe1.tol a < 5 := by decide +kernel
theorem period_defect1 : ∀ a : Fin N, 3 ≤ a.val → 0 < periodRecipe1.tol a →
    SensitivityQ.DefectBound periodTournament periodLabeling.label (periodRecipe1.tol a) (v (periodRecipe1.tol a)) := by
  intro a ha _
  exact SensitivitySourceLabelsBelow14567.cyclic_defect D (by decide +kernel) (by decide +kernel) (periodRecipe1.tol a) (period_tolerance_bound1 a ha)

theorem compatible1 : SensitivityNQ.Compatible periodRecipe1 P1Z P1Y := by
  unfold SensitivityNQ.Compatible
  decide +kernel
theorem certificateZ1 : ∀ i j : Fin N, i ≤ j →
    let b := witnessZ1 i j
    i ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ j ∧
      SensitivityNQ.rawZeroSourceCombined K t v w periodRecipe1 P1Z P1Y b.1 b.2 ≤ P2Z i j := by decide +kernel
theorem certificateY1 : ∀ i j : Fin N, i ≤ j →
    let b := witnessY1 i j
    i ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ j ∧
      SensitivityNQ.rawOne D periodRecipe1 P1Z P1Y b.1 b.2 ≤ P2Y i j := by decide +kernel
def step1 {I : Type} (F : Fin N → (I → Bool) → Bool) :
    Fin N → (((Fin K × Fin 2) × I) → Bool) → Bool :=
  SensitivityNQ.stage periodTournament periodLabeling.label periodRecipe1 F
theorem step1_nested {I : Type} {F : Fin N → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (step1 F) :=
  SensitivityNQ.stage_nested periodTournament periodLabeling.label periodRecipe1 period_valid1 F hF

def periodRecipe2 : SensitivityNQ.Recipe N := ⟨![6, 7, 7, 7, 8, 9, 9, 9, 10, 10, 11, 12, 13, 14, 15, 15], ![14, 14, 14, 7, 7, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0], ![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
theorem period_valid2 : periodRecipe2.Valid := by
  unfold SensitivityNQ.Recipe.Valid Monotone
  decide +kernel
theorem period_tolerance_bound2 : ∀ a : Fin N, 3 ≤ a.val → periodRecipe2.tol a < 5 := by decide +kernel
theorem period_defect2 : ∀ a : Fin N, 3 ≤ a.val → 0 < periodRecipe2.tol a →
    SensitivityQ.DefectBound periodTournament periodLabeling.label (periodRecipe2.tol a) (v (periodRecipe2.tol a)) := by
  intro a ha _
  exact SensitivitySourceLabelsBelow14567.cyclic_defect D (by decide +kernel) (by decide +kernel) (periodRecipe2.tol a) (period_tolerance_bound2 a ha)

theorem compatible2 : SensitivityNQ.Compatible periodRecipe2 P2Z P2Y := by
  unfold SensitivityNQ.Compatible
  decide +kernel
theorem certificateZ2 : ∀ i j : Fin N, i ≤ j →
    let b := witnessZ2 i j
    i ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ j ∧
      SensitivityNQ.rawZeroSourceCombined K t v w periodRecipe2 P2Z P2Y b.1 b.2 ≤ P3Z i j := by decide +kernel
theorem certificateY2 : ∀ i j : Fin N, i ≤ j →
    let b := witnessY2 i j
    i ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ j ∧
      SensitivityNQ.rawOne D periodRecipe2 P2Z P2Y b.1 b.2 ≤ P3Y i j := by decide +kernel
def step2 {I : Type} (F : Fin N → (I → Bool) → Bool) :
    Fin N → (((Fin K × Fin 2) × I) → Bool) → Bool :=
  SensitivityNQ.stage periodTournament periodLabeling.label periodRecipe2 F
theorem step2_nested {I : Type} {F : Fin N → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (step2 F) :=
  SensitivityNQ.stage_nested periodTournament periodLabeling.label periodRecipe2 period_valid2 F hF

def periodRecipe3 : SensitivityNQ.Recipe N := ⟨![6, 7, 7, 7, 8, 9, 9, 9, 10, 10, 11, 12, 13, 14, 15, 15], ![14, 14, 14, 7, 7, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0], ![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
theorem period_valid3 : periodRecipe3.Valid := by
  unfold SensitivityNQ.Recipe.Valid Monotone
  decide +kernel
theorem period_tolerance_bound3 : ∀ a : Fin N, 3 ≤ a.val → periodRecipe3.tol a < 5 := by decide +kernel
theorem period_defect3 : ∀ a : Fin N, 3 ≤ a.val → 0 < periodRecipe3.tol a →
    SensitivityQ.DefectBound periodTournament periodLabeling.label (periodRecipe3.tol a) (v (periodRecipe3.tol a)) := by
  intro a ha _
  exact SensitivitySourceLabelsBelow14567.cyclic_defect D (by decide +kernel) (by decide +kernel) (periodRecipe3.tol a) (period_tolerance_bound3 a ha)

theorem compatible3 : SensitivityNQ.Compatible periodRecipe3 P3Z P3Y := by
  unfold SensitivityNQ.Compatible
  decide +kernel
theorem certificateZ3 : ∀ i j : Fin N, i ≤ j →
    let b := witnessZ3 i j
    i ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ j ∧
      SensitivityNQ.rawZeroSourceCombined K t v w periodRecipe3 P3Z P3Y b.1 b.2 ≤ (fun i j => VZ i j*R) i j := by decide +kernel
theorem certificateY3 : ∀ i j : Fin N, i ≤ j →
    let b := witnessY3 i j
    i ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ j ∧
      SensitivityNQ.rawOne D periodRecipe3 P3Z P3Y b.1 b.2 ≤ (fun i j => VY i j*R) i j := by decide +kernel
def step3 {I : Type} (F : Fin N → (I → Bool) → Bool) :
    Fin N → (((Fin K × Fin 2) × I) → Bool) → Bool :=
  SensitivityNQ.stage periodTournament periodLabeling.label periodRecipe3 F
theorem step3_nested {I : Type} {F : Fin N → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (step3 F) :=
  SensitivityNQ.stage_nested periodTournament periodLabeling.label periodRecipe3 period_valid3 F hF

abbrev CycleCoord (I : Type) : Type := (Fin K × Fin 2) × ((Fin K × Fin 2) × ((Fin K × Fin 2) × ((Fin K × Fin 2) × (I))))
def cycleStep {I : Type} (F : Fin N → (I → Bool) → Bool) :
    Fin N → (CycleCoord I → Bool) → Bool := step3 (step2 (step1 (step0 (F))))
theorem cycle_nested {I : Type} {F : Fin N → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (cycleStep F) := step3_nested (step2_nested (step1_nested (step0_nested (hF))))

theorem cycle_bounds {I : Type} [Fintype I]
    (F : Fin N → (I → Bool) → Bool) (hF : NestedFamily F) (u : ℕ)
    (hz : PairBound F false (fun i j => VZ i j*u))
    (hy : PairBound F true (fun i j => VY i j*u)) :
    PairBound (cycleStep F) false (fun i j => VZ i j*(R*u)) ∧
    PairBound (cycleStep F) true (fun i j => VY i j*(R*u)) := by
  have hstage0 : PairBound (step0 (F)) false (fun i j => P1Z i j*u) ∧
      PairBound (step0 (F)) true (fun i j => P1Y i j*u) := by
    apply SensitivitySourceCombinedPeriodic.profile_step_bounds periodTournament periodLabeling (by decide +kernel) v rfl w (by decide +kernel) source_bound
      (cyclicTournament_outdegree D) periodRecipe0 period_valid0 period_defect0
      VZ VY P1Z P1Y compatible0 _ _ (F) (hF) u hz hy
    · intro i j hij
      exact ⟨(witnessZ0 i j).1,(witnessZ0 i j).2,certificateZ0 i j hij⟩
    · intro i j hij
      exact ⟨(witnessY0 i j).1,(witnessY0 i j).2,certificateY0 i j hij⟩
  have hstage1 : PairBound (step1 (step0 (F))) false (fun i j => P2Z i j*u) ∧
      PairBound (step1 (step0 (F))) true (fun i j => P2Y i j*u) := by
    apply SensitivitySourceCombinedPeriodic.profile_step_bounds periodTournament periodLabeling (by decide +kernel) v rfl w (by decide +kernel) source_bound
      (cyclicTournament_outdegree D) periodRecipe1 period_valid1 period_defect1
      P1Z P1Y P2Z P2Y compatible1 _ _ (step0 (F)) (step0_nested (hF)) u hstage0.1 hstage0.2
    · intro i j hij
      exact ⟨(witnessZ1 i j).1,(witnessZ1 i j).2,certificateZ1 i j hij⟩
    · intro i j hij
      exact ⟨(witnessY1 i j).1,(witnessY1 i j).2,certificateY1 i j hij⟩
  have hstage2 : PairBound (step2 (step1 (step0 (F)))) false (fun i j => P3Z i j*u) ∧
      PairBound (step2 (step1 (step0 (F)))) true (fun i j => P3Y i j*u) := by
    apply SensitivitySourceCombinedPeriodic.profile_step_bounds periodTournament periodLabeling (by decide +kernel) v rfl w (by decide +kernel) source_bound
      (cyclicTournament_outdegree D) periodRecipe2 period_valid2 period_defect2
      P2Z P2Y P3Z P3Y compatible2 _ _ (step1 (step0 (F))) (step1_nested (step0_nested (hF))) u hstage1.1 hstage1.2
    · intro i j hij
      exact ⟨(witnessZ2 i j).1,(witnessZ2 i j).2,certificateZ2 i j hij⟩
    · intro i j hij
      exact ⟨(witnessY2 i j).1,(witnessY2 i j).2,certificateY2 i j hij⟩
  have hstage3 : PairBound (step3 (step2 (step1 (step0 (F))))) false (fun i j => (VZ i j*R)*u) ∧
      PairBound (step3 (step2 (step1 (step0 (F))))) true (fun i j => (VY i j*R)*u) := by
    apply SensitivitySourceCombinedPeriodic.profile_step_bounds periodTournament periodLabeling (by decide +kernel) v rfl w (by decide +kernel) source_bound
      (cyclicTournament_outdegree D) periodRecipe3 period_valid3 period_defect3
      P3Z P3Y (fun i j => VZ i j*R) (fun i j => VY i j*R) compatible3 _ _ (step2 (step1 (step0 (F)))) (step2_nested (step1_nested (step0_nested (hF)))) u hstage2.1 hstage2.2
    · intro i j hij
      exact ⟨(witnessZ3 i j).1,(witnessZ3 i j).2,certificateZ3 i j hij⟩
    · intro i j hij
      exact ⟨(witnessY3 i j).1,(witnessY3 i j).2,certificateY3 i j hij⟩
  simpa only [cycleStep,Nat.mul_assoc] using hstage3

abbrev InitialCoord := Fin 1
def initial (_ : Fin N) : (InitialCoord → Bool) → Bool := fun x => x 0
theorem initial_nested : NestedFamily initial := by
  constructor
  intro i j x hij hx
  exact hx
theorem initial_bounds : PairBound initial false VZ ∧ PairBound initial true VY := by
  have hs (x : Fin 1 → Bool) :
      jointSensitivityAt (fun y : Fin 1 → Bool => y 0) (fun y => y 0) x ≤ 1 := by
    simpa only [joint_self,Fintype.card_fin] using sensitivityAt_le_card (fun y : Fin 1 → Bool => y 0) x
  constructor
  · intro i j hij x hi hj
    exact (hs x).trans (initial_positive i j hij).1
  · intro i j hij x hi hj
    exact (hs x).trans (initial_positive i j hij).2

def initialBlocks : Blocks initial 1 where
  zero _ := rfl
  sets _ := {0}
  nonempty _ := Finset.singleton_nonempty _
  disjoint := by
    intro i j hij
    have he : i = j := by
      apply Fin.ext
      have hi : i.val < 1 := i.isLt
      have hj : j.val < 1 := j.isLt
      omega
    exact False.elim (hij he)
  on := by
    intro a i
    simp [initial,OAI.Paper320.flip]

def RepeatCoord : ℕ → Type
  | 0 => InitialCoord
  | m+1 => CycleCoord (RepeatCoord m)
instance repeatFintype (m : ℕ) : Fintype (RepeatCoord m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype InitialCoord)
  | succ m ih => exact inferInstanceAs (Fintype (CycleCoord (RepeatCoord m)))

def repeated : (m : ℕ) → Fin N → (RepeatCoord m → Bool) → Bool
  | 0 => initial
  | m+1 => cycleStep (repeated m)
theorem repeated_nested (m : ℕ) : NestedFamily (repeated m) := by
  induction m with
  | zero => exact initial_nested
  | succ m ih => exact cycle_nested ih
theorem repeated_bounds (m : ℕ) :
    PairBound (repeated m) false (fun i j => VZ i j*R^m) ∧
    PairBound (repeated m) true (fun i j => VY i j*R^m) := by
  induction m with
  | zero =>
    change PairBound initial false (fun i j => VZ i j*R^0) ∧ PairBound initial true (fun i j => VY i j*R^0)
    simpa only [pow_zero,Nat.mul_one] using initial_bounds
  | succ m ih =>
    change PairBound (cycleStep (repeated m)) false (fun i j => VZ i j*R^(m+1)) ∧
      PairBound (cycleStep (repeated m)) true (fun i j => VY i j*R^(m+1))
    have h := cycle_bounds (repeated m) (repeated_nested m) (R^m) ih.1 ih.2
    simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

def step0Blocks {I : Type} {F : Fin N → (I → Bool) → Bool} {n : ℕ}
    (b : Blocks F n) : Blocks (step0 F) (K*n) := by
  unfold step0
  exact SensitivitySourceCombinedPeriodic.stage_blocks _ _ _ F b
def step1Blocks {I : Type} {F : Fin N → (I → Bool) → Bool} {n : ℕ}
    (b : Blocks F n) : Blocks (step1 F) (K*n) := by
  unfold step1
  exact SensitivitySourceCombinedPeriodic.stage_blocks _ _ _ F b
def step2Blocks {I : Type} {F : Fin N → (I → Bool) → Bool} {n : ℕ}
    (b : Blocks F n) : Blocks (step2 F) (K*n) := by
  unfold step2
  exact SensitivitySourceCombinedPeriodic.stage_blocks _ _ _ F b
def step3Blocks {I : Type} {F : Fin N → (I → Bool) → Bool} {n : ℕ}
    (b : Blocks F n) : Blocks (step3 F) (K*n) := by
  unfold step3
  exact SensitivitySourceCombinedPeriodic.stage_blocks _ _ _ F b
def repeatedBlocks : (m : ℕ) → Blocks (repeated m) (G^m)
  | 0 => by
      change Blocks initial 1
      exact initialBlocks
  | m+1 => by
      change Blocks (cycleStep (repeated m)) (G^(m+1))
      have h := step3Blocks (step2Blocks (step1Blocks (step0Blocks (repeatedBlocks m))))
      have hc : K*(K*(K*(K*(G^m)))) = G^(m+1) := by
        rw [pow_succ G m]
        simp only [G]
        ring
      simpa only [cycleStep,hc] using h

theorem repeated_sensitivity (m : ℕ) : sensitivity (repeated m output) ≤ C*R^m := by
  apply sensitivity_le
  intro x
  cases hx : repeated m output x
  · exact ((repeated_bounds m).1.self output x hx).trans (Nat.mul_le_mul_right _ final_bounds.1)
  · exact ((repeated_bounds m).2.self output x hx).trans (Nat.mul_le_mul_right _ final_bounds.2)
theorem repeated_blocksensitivity (m : ℕ) : G^m ≤ blockSensitivityAt (repeated m output) (fun _ => false) := by
  have b := repeatedBlocks m
  simpa only [Fintype.card_fin] using
    le_blockSensitivityAt_of_family (repeated m output) (fun _ => false)
      b.sets b.nonempty b.disjoint (fun i => by rw [b.on output i,b.zero output]; decide)
theorem finite_seed (m : ℕ) : ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
    sensitivity f ≤ C*R^m ∧ G^m ≤ blockSensitivityAt f (fun _ => false) := by
  let e := Fintype.equivFin (RepeatCoord m)
  refine ⟨Fintype.card (RepeatCoord m), reindex e (repeated m output), ?_, ?_⟩
  · rw [sensitivity_reindex]
    exact repeated_sensitivity m
  · rw [blockSensitivityAt_reindex]
    exact repeated_blocksensitivity m

theorem one_lt_C : 1 < C := by decide +kernel
theorem one_lt_R : 1 < R := by decide +kernel
theorem one_lt_G : 1 < G := by decide +kernel




theorem public_previous_power_lt : (25260794820729601 : ℕ)^23 < 50063523^49 := by decide +kernel
theorem new_power_lt : R^49 < G^23 := by decide +kernel
end
end SourceCombined14055P4
end



/- Component: Research.ExponentFromSeeds -/
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open OAI.Paper320
namespace SensitivityPeriodicLog

/-- Every exponent below the growth-rate ratio follows from genuine finite seeds. -/
theorem achieves_strict (c r g : ℕ) (β : ℝ)
    (hc : 1 < c) (hr : 1 < r) (hg : 1 < g) (hβ : 0 ≤ β)
    (hstrict : β < Real.log (g : ℝ) / Real.log (r : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ c * r ^ m ∧ g ^ m ≤ blockSensitivityAt f (fun _ => false)) :
    SensitivityCampaign.AchievesExponent β := by
  have hcp : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hgp : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hlr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  have hgap : 0 < Real.log (g : ℝ) - β * Real.log (r : ℝ) := by
    have hh := (lt_div_iff₀ hlr).mp hstrict
    linarith
  let δ := Real.log (g : ℝ) - β * Real.log (r : ℝ)
  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (β * Real.log (c : ℝ) / δ))
  have hmposr : (0 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hmpos : 0 < m := by exact_mod_cast hmposr
  have hmul : β * Real.log (c : ℝ) < (m : ℝ) * δ :=
    (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt hm)
  obtain ⟨n, f, hs, hb⟩ := hseed m
  have hA : 1 < c * r ^ m :=
    hc.trans_le (Nat.le_mul_of_pos_right c (pow_pos (by omega : 0 < r) m))
  have hB : 1 < g ^ m := one_lt_pow₀ hg (Nat.ne_of_gt hmpos)
  apply SensitivityCampaign.finite_certificate f (fun _ => false)
    (c * r ^ m) (g ^ m) β hA hB hβ hs hb
  have hrp : (0 : ℝ) < r := by linarith
  have hp : (0 : ℝ) < (c * r ^ m : ℕ) := by exact_mod_cast (by omega : 0 < c * r ^ m)
  have hbp : (0 : ℝ) < (g ^ m : ℕ) := by exact_mod_cast (by omega : 0 < g ^ m)
  apply (Real.rpow_le_iff_le_log hp hbp).2
  push_cast
  rw [Real.log_mul (ne_of_gt hcp) (ne_of_gt (pow_pos hrp m)),
    Real.log_pow, Real.log_pow]
  dsimp only [δ] at hmul
  nlinarith

/-- The campaign endpoint includes arbitrary positive exponent loss, so the
exact logarithmic growth-rate ratio itself is attained in that sense. -/
theorem achieves_limit (c r g : ℕ)
    (hc : 1 < c) (hr : 1 < r) (hg : 1 < g)
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ c * r ^ m ∧ g ^ m ≤ blockSensitivityAt f (fun _ => false)) :
    SensitivityCampaign.AchievesExponent (Real.log (g : ℝ) / Real.log (r : ℝ)) := by
  let a := Real.log (g : ℝ) / Real.log (r : ℝ)
  have ha : 0 < a := div_pos (Real.log_pos (by exact_mod_cast hg))
    (Real.log_pos (by exact_mod_cast hr))
  intro ε hε S hS
  let β := max 0 (a - ε / 2)
  have hβ : 0 ≤ β := le_max_left _ _
  have hb : β < a := max_lt ha (by linarith)
  have hres := achieves_strict c r g β hc hr hg hβ hb hseed
  obtain ⟨n, f, hs, hp⟩ := hres (ε / 2) (by linarith) S hS
  refine ⟨n, f, hs, ?_⟩
  have hbase : (1 : ℝ) ≤ sensitivity f := by
    exact_mod_cast (show 1 ≤ sensitivity f by omega)
  have he : a - ε ≤ β - ε / 2 := by
    have hh := le_max_right 0 (a - ε / 2)
    dsimp only [β]
    linarith
  exact (Real.rpow_le_rpow_of_exponent_le hbase he).trans hp
end SensitivityPeriodicLog

namespace SensitivityPeriodicLog




end SensitivityPeriodicLog
end



/- Component: Research.ExponentPowerComparison -/
section
set_option autoImplicit false

namespace SensitivityPeriodicLog

theorem rate_lt_rational_of_pow_lt (g r p q : ℕ)
    (hg : 1 < g) (hr : 1 < r) (hq : 0 < q)
    (hpow : g^q < r^p) :
    Real.log (g : ℝ) / Real.log (r : ℝ) < (p : ℝ) / (q : ℝ) := by
  have hgp : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hpowr : (g : ℝ)^q < (r : ℝ)^p := by exact_mod_cast hpow
  have hlogs := Real.log_lt_log (pow_pos hgp q) hpowr
  rw [Real.log_pow, Real.log_pow] at hlogs
  apply (div_lt_div_iff₀ (Real.log_pos hr1) hqp).2
  nlinarith

theorem rational_lt_rate_of_pow_lt (g r p q : ℕ)
    (hg : 1 < g) (hr : 1 < r) (hq : 0 < q)
    (hpow : r^p < g^q) :
    (p : ℝ) / (q : ℝ) < Real.log (g : ℝ) / Real.log (r : ℝ) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hpowr : (r : ℝ)^p < (g : ℝ)^q := by exact_mod_cast hpow
  have hlogs := Real.log_lt_log (pow_pos hrp p) hpowr
  rw [Real.log_pow, Real.log_pow] at hlogs
  apply (div_lt_div_iff₀ hqp (Real.log_pos hr1)).2
  nlinarith

theorem growth_rate_strict_of_power_bridge (g r g' r' p q : ℕ)
    (hg : 1 < g) (hr : 1 < r) (hg' : 1 < g') (hr' : 1 < r') (hq : 0 < q)
    (hold : g^q < r^p) (hnew : r'^p < g'^q) :
    Real.log (g : ℝ) / Real.log (r : ℝ) <
      Real.log (g' : ℝ) / Real.log (r' : ℝ) :=
  (rate_lt_rational_of_pow_lt g r p q hg hr hq hold).trans
    (rational_lt_rate_of_pow_lt g' r' p q hg' hr' hq hnew)

end SensitivityPeriodicLog
end



/- Component: Research.SourceCombined14055P4Endpoint -/
section
set_option autoImplicit false
namespace SourceCombined14055P4

theorem achieves_endpoint : SensitivityCampaign.AchievesExponent
    (Real.log (G : ℝ) / Real.log (R : ℝ)) :=
  SensitivityPeriodicLog.achieves_limit C R G one_lt_C one_lt_R one_lt_G finite_seed

theorem endpoint_strict_improvement :
    Real.log ((25260794820729601 : ℕ) : ℝ) / Real.log ((50063523 : ℕ) : ℝ) <
      Real.log (G : ℝ) / Real.log (R : ℝ) :=
  SensitivityPeriodicLog.growth_rate_strict_of_power_bridge
    25260794820729601 50063523 G R 49 23
    (by decide +kernel) (by decide +kernel) one_lt_G one_lt_R (by decide +kernel)
    public_previous_power_lt new_power_lt

theorem closed_result :
    SensitivityCampaign.AchievesExponent
      (Real.log (39023246726150625 : ℝ) / Real.log (61141556 : ℝ)) ∧
    (Real.log (25260794820729601 : ℝ) / Real.log (50063523 : ℝ) <
      Real.log (39023246726150625 : ℝ) / Real.log (61141556 : ℝ)) := by
  have ha := achieves_endpoint
  have hi := endpoint_strict_improvement
  norm_num [G,K,R] at ha hi ⊢
  exact ⟨ha,hi⟩

end SourceCombined14055P4
end



theorem solution : SensitivityCampaign.AchievesExponent
      (Real.log (39023246726150625 : ℝ) / Real.log (61141556 : ℝ)) ∧
    (Real.log (25260794820729601 : ℝ) / Real.log (50063523 : ℝ) <
      Real.log (39023246726150625 : ℝ) / Real.log (61141556 : ℝ)) := by
  exact ⟨SourceCombined14055P4.achieves_endpoint, SourceCombined14055P4.endpoint_strict_improvement⟩
#print axioms solution

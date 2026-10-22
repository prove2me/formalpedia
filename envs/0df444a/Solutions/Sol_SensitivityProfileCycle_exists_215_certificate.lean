-- Prove2me | solution 1 for SensitivityProfileCycle.exists_215_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-10-21T22:18:50.166992+00:00
-- url     : https://prove2.me/submissions/683c2997-8a99-4635-b8f3-8b28d187f5f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SensitivityProfileSearch
import Theorems.Thm_SensitivityProfileSearch_exists_215_orbit


/-!
The shared q=0,...,5 labeling argument is retained from accepted Prove2Me
submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, by yousofy with Codex.
It retains the attributed OpenAI/math, Robin Kothari with Codex, and
earlier community foundations.  The final bridge below specializes the
proved labeling to the cyclic tournament with 14055 vertices, in the
exact interface used by SensitivityProfileCycle.Certificate.
-/

set_option Elab.async false
set_option linter.all false
namespace ProfileLabelingCache

/- Component: RowPatternCountingFast -/
section
/-!
Generic finite counting step behind the sharper tournament labeling
certificate, retained from the accepted source and checked locally.

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

/- Component: Research.Source14055Q5Arithmetic -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 4096
open scoped Classical BigOperators

namespace SensitivitySourceLabeling14055Q5.Arithmetic

abbrev K : ℕ := 14055
abbrev D : ℕ := 7027

def cutoff (q : Fin 6) : ℕ := ![24,31,38,44,50,55] q

def q5Product : ℕ := 101584 ^ 55

theorem q5_tangents : ∀ d : Fin 55,
    SharperRowCounting.rowPatterns 5 d.val * 101584 ^ d.val * 122438 ^ 27 ≤
      101584 ^ 28 * 122438 ^ d.val := by
  decide

def ordinaryProbability (q : Fin 6) : ℚ :=
  if h : q.val < 5 then
    if q.val = 0 then ((2^24 : ℕ) : ℚ) / ((2^276 : ℕ) : ℚ)
    else SensitivityRowCounting.rowProbability 0 ⟨q.val,h⟩
  else ((2^55 * q5Product : ℕ) : ℚ) / ((2^1485 : ℕ) : ℚ)

def size (q : Fin 7) : ℕ :=
  if h : q.val < 6 then cutoff ⟨q.val,h⟩ else 22

def tolerance (q : Fin 7) : ℕ := if q.val < 6 then q.val else 0

def degree (q : Fin 7) : ℕ := (size q).choose 2

def tag (q : Fin 7) : ℕ :=
  if h : q.val < 5 then
    if q.val = 0 then 2^24 else SharperRowLLL.tags 0 ⟨q.val,h⟩
  else if q.val = 5 then 2^55 * q5Product else 2^21

def coefficientChoose (q : Fin 7) : ℕ :=
  if q.val < 6 then (K-2).choose (size q-2) else 21 * (D-1).choose 20

def coefficient (q : Fin 7) : ℕ :=
  if q.val < 6 then
    (K-2).descFactorial (size q-2) / (size q-2).factorial
  else 21 * ((D-1).descFactorial 20 / (20 : ℕ).factorial)

def probability (q : Fin 7) : ℚ :=
  if h : q.val < 6 then ordinaryProbability ⟨q.val,h⟩
  else ((2^21 : ℕ) : ℚ) / ((2^231 : ℕ) : ℚ)

theorem elementary (q : Fin 7) : 3 ≤ size q ∧ size q ≤ K ∧ degree q ≤ 1485 := by
  fin_cases q <;> decide

theorem coefficient_exact (q : Fin 7) : coefficientChoose q = coefficient q := by
  unfold coefficientChoose coefficient
  split_ifs <;> rw [Nat.choose_eq_descFactorial_div_factorial]

theorem coefficient_pos (q : Fin 7) : 1 ≤ coefficientChoose q := by
  unfold coefficientChoose
  split_ifs with h
  · apply Nat.choose_pos
    exact Nat.sub_le_sub_right (elementary q).2.1 2
  · have hc : 1 ≤ (D-1).choose 20 := Nat.choose_pos (by decide)
    omega

theorem integer_budget :
    658 * (∑ q : Fin 7, coefficient q * tag q * 329 ^ degree q *
      656 ^ (1485-degree q)) ≤ 2 * 656 ^ 1485 := by
  decide

theorem probability_as_tag (q : Fin 7) :
    probability q = ((tag q : ℕ) : ℚ) / ((2 ^ degree q : ℕ) : ℚ) := by
  fin_cases q <;> rfl

theorem probability_nonneg (q : Fin 7) : 0 ≤ probability q := by
  rw [probability_as_tag]
  positivity

theorem activity_double (q : Fin 7) :
    probability q * ((329 : ℚ)/328) ^ degree q =
      (tag q : ℚ) * ((329 : ℚ)/656) ^ degree q := by
  rw [probability_as_tag]
  simpa only [show (2*329 : ℕ) = 658 by decide, Nat.cast_ofNat,
    show ((658 : ℚ)/656) = (329 : ℚ)/328 by norm_num] using
    SensitivityRowCounting.activity_double (tag q) (degree q) 329 656 (by decide)

theorem activity_budget :
    ∑ q : Fin 7, (coefficientChoose q : ℚ) *
      (probability q * ((329 : ℚ)/328) ^ degree q) ≤ 1 - 1 / ((329 : ℚ)/328) := by
  have h := SensitivityLabelCache12607.SensitivityLLL.rational_power_budget
    coefficient tag degree 1485 329 656 658 (by decide) (by decide)
    (fun q => (elementary q).2.2) integer_budget (by decide)
  simp_rw [coefficient_exact, activity_double]
  convert h using 1 <;> norm_num





end SensitivitySourceLabeling14055Q5.Arithmetic
end

/- Component: Research.Source14055Q5SharedLabeling -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped Classical BigOperators

namespace SensitivitySourceLabeling14055Q5
noncomputable section

open SensitivityLabelCache12607.OAI.Paper320
open SensitivityLabelCache12607.SensitivityQLLL
open SensitivityLabelCache12607.SensitivityCylinder
open Arithmetic
open SensitivitySourceLabeling

def family {k : ℕ} (T : Tournament k) (q : Fin 7) : Finset (Finset (Fin k)) :=
  if q.val < 6 then Finset.univ.powersetCard (size q) else sourceSets T 22

theorem family_card {k : ℕ} (T : Tournament k) (q : Fin 7) (I : Finset (Fin k))
    (hI : I ∈ family T q) : I.card = size q := by
  by_cases hq : q.val < 6
  · exact (Finset.mem_powersetCard.mp (by simpa only [family, if_pos hq] using hI)).2
  · have h := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp
        (by simpa only [family, if_neg hq] using hI : I ∈ sourceSets T 22)).1).2
    simpa only [size, dif_neg hq] using h

def JointIndex {k : ℕ} (T : Tournament k) := Σ q : Fin 7, family T q

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

theorem q5_row_product_bound {k : ℕ} (T : Tournament k)
    (I : Finset (Fin k)) (hI : I.card = 55) :
    (∏ i : I, SharperRowCounting.rowPatterns 5
      (SensitivityRowCounting.rows T I i).card) ≤ q5Product := by
  have hs : (∑ i : I, (SensitivityRowCounting.rows T I i).card) =
      27 * Fintype.card I + 0 := by
    rw [SensitivityRowCounting.rows_card_sum, Fintype.card_coe, hI]
    decide
  have ht (i : I) :
      SharperRowCounting.rowPatterns 5 (SensitivityRowCounting.rows T I i).card *
        101584 ^ (SensitivityRowCounting.rows T I i).card * 122438 ^ 27 ≤
      101584 ^ 28 * 122438 ^ (SensitivityRowCounting.rows T I i).card := by
    have hi : (SensitivityRowCounting.rows T I i).card < 55 := by
      simpa only [hI] using SensitivityRowCounting.rows_card_lt T I i
    exact q5_tangents ⟨_,hi⟩
  have hp := SharperRowCounting.balanced_product_le
    (fun i : I => (SensitivityRowCounting.rows T I i).card)
    (fun i : I => SharperRowCounting.rowPatterns 5
      (SensitivityRowCounting.rows T I i).card)
    27 0 101584 122438 (Nat.zero_le _) (by decide) (by decide) hs ht
  simpa only [Fintype.card_coe, hI, Nat.sub_zero, pow_zero, mul_one,
    q5Product] using hp

theorem localBad_q5_row_count {k : ℕ} (T : Tournament k)
    (I : Finset (Fin k)) (hI : I.card = 55) :
    (localBad T 5 I).card ≤
      2 ^ I.card * (q5Product * 2 ^ (k*k-I.card.choose 2)) := by
  let encoded : Finset (EdgeAssignment k) :=
    (Finset.univ : Finset (I → Fin 2)).biUnion fun m =>
      SharperRowCounting.rowGood (SensitivityRowCounting.rows T I)
        (fun _ => 5) (SensitivityRowCounting.extendedColor I m)
  have hc : localBad T 5 I ⊆ encoded := by
    intro a ha
    obtain ⟨m, hm⟩ := (Finset.mem_filter.mp ha).2
    refine Finset.mem_biUnion.mpr
      ⟨(fun j => m j.val), by simp only [Finset.mem_univ], ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨by simp only [Finset.mem_univ], ?_⟩
    intro i
    rw [SensitivityRowCounting.rows_filter_card]
    convert hm i.val i.property using 1
    congr 1
    apply Finset.filter_congr
    intro j hj
    simp only [SensitivityRowCounting.extendedColor, dif_pos hj]
  have hg (m : I → Fin 2) :
      (SharperRowCounting.rowGood (SensitivityRowCounting.rows T I)
        (fun _ => 5) (SensitivityRowCounting.extendedColor I m)).card ≤
      2 ^ (k*k-I.card.choose 2) * q5Product := by
    have h := SharperRowCounting.rowGood_card_le
      (SensitivityRowCounting.rows T I) (fun _ => 5)
      (SensitivityRowCounting.extendedColor I m)
    rw [SensitivityRowCounting.rows_union, T.card_internalEdges] at h
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact h.trans (Nat.mul_le_mul_left _ (q5_row_product_bound T I hI))
  apply (Finset.card_le_card hc).trans
  apply Finset.card_biUnion_le.trans
  calc
    (∑ m : I → Fin 2,
        (SharperRowCounting.rowGood (SensitivityRowCounting.rows T I)
          (fun _ => 5) (SensitivityRowCounting.extendedColor I m)).card) ≤
      ∑ _m : I → Fin 2, 2 ^ (k*k-I.card.choose 2) * q5Product :=
        Finset.sum_le_sum (fun m _ => hg m)
    _ = 2 ^ I.card * (q5Product * 2 ^ (k*k-I.card.choose 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_coe, Fintype.card_fin, smul_eq_mul]
      ring

theorem localBad_q5_row_probability {k : ℕ} (T : Tournament k)
    (I : Finset (Fin k)) (hI : I.card = 55) :
    ((localBad T 5 I).card : ℚ) ≤
      (((2 ^ 55 * q5Product : ℕ) : ℚ) / ((2 ^ 1485 : ℕ) : ℚ)) *
        Fintype.card (EdgeAssignment k) := by
  have hroom : I.card.choose 2 ≤ k*k := by
    rw [← T.card_internalEdges I]
    simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (T.internalEdges I))
  have hpow : (2 : ℚ) ^ I.card.choose 2 * 2 ^ (k*k-I.card.choose 2) =
      2 ^ (k*k) := by
    rw [← pow_add, Nat.add_sub_cancel' hroom]
  calc
    ((localBad T 5 I).card : ℚ) ≤
        (2 : ℚ) ^ I.card * ((q5Product : ℚ) * 2 ^ (k*k-I.card.choose 2)) := by
      exact_mod_cast localBad_q5_row_count T I hI
    _ = (((2 ^ 55 * q5Product : ℕ) : ℚ) / ((2 ^ 1485 : ℕ) : ℚ)) *
        Fintype.card (EdgeAssignment k) := by
      simp only [EdgeAssignment, Fintype.card_fun, Fintype.card_prod,
        Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      have hE : I.card.choose 2 = 1485 := by rw [hI]; decide
      rw [← hI, ← hE]
      field_simp
      rw [← hpow]
      ring

theorem localBad_ordinary_probability {k : ℕ} (q : Fin 6) (T : Tournament k)
    (I : Finset (Fin k)) (hI : I.card = cutoff q) :
    ((localBad T q.val I).card : ℚ) ≤
      ordinaryProbability q * Fintype.card (EdgeAssignment k) := by
  fin_cases q
  · have hcard : I.card = 24 := hI
    change ((localBad T 0 I).card : ℚ) ≤
      (((2^24 : ℕ) : ℚ) / ((2^276 : ℕ) : ℚ)) * Fintype.card (EdgeAssignment k)
    simpa only [SensitivityLabelCache12607.SensitivityQLLL.eventProbability,
      hcard, Nat.zero_mul, pow_zero, mul_one,
      EdgeAssignment, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      show (24 : ℕ).choose 2 = 276 by decide] using
      localBad_probability_bound T 0 I
  · exact SensitivityRowCounting.localBad_row_probability 0 ⟨1,by decide⟩ T I hI
  · exact SensitivityRowCounting.localBad_row_probability 0 ⟨2,by decide⟩ T I hI
  · exact SensitivityRowCounting.localBad_row_probability 0 ⟨3,by decide⟩ T I hI
  · exact SensitivityRowCounting.localBad_row_probability 0 ⟨4,by decide⟩ T I hI
  · exact localBad_q5_row_probability T I hI

theorem bad_probability {k : ℕ} (T : Tournament k) (i : JointIndex T) :
    ((bad T i).card : ℚ) ≤ probability i.1 * Fintype.card (EdgeAssignment k) := by
  by_cases hq : i.1.val < 6
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
    (i : JointIndex T) (q : Fin 7) :
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
  by_cases hq : q.val < 6
  · have hb := SensitivityLabelCache12607.SensitivityLLL.card_overlap_two_fin_le
      k i.2.val (size q) (by have h := (elementary q).1; omega)
    have hk : k ≤ K := by
      change d ≤ 7027 at hdhi
      change k ≤ 14055
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
  let x : Fin 7 → ℚ := fun q => probability q * γ ^ degree q
  have hγ : 1 < γ := by norm_num [γ]
  have hx0 (q : Fin 7) : 0 ≤ x q :=
    mul_nonneg (probability_nonneg q) (pow_nonneg (by norm_num [γ]) _)
  have hx1 : ∀ q : Fin 7, x q < 1 :=
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
      (∀ q : Fin 6, SensitivityLabelCache12607.SensitivityQ.DefectBound T label q.val
        (cutoff q)) ∧
      (∀ I : Finset (Fin k), ∀ m : Fin k → Fin 2, HasSource T I →
        (∀ i ∈ I, (I.filter (fun j => T.Adj i j ∧ label i j ≠ m j)).card ≤ 0) →
          I.card < 22) := by
  refine ⟨(fun i j => a (i,j)), ?_, ?_⟩
  · intro q I m hrow
    by_contra hI
    obtain ⟨J,hJI,hJ⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hI)
    let p : Fin 7 := ⟨q.val, by have h := q.isLt; omega⟩
    have hp : p.val < 6 := q.isLt
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
    have hmem : J ∈ family T 6 := by
      simp only [family, show ¬ ((6 : Fin 7).val < 6) by decide, if_false]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hJ⟩, hsrcJ⟩
    let j : JointIndex T := ⟨6,⟨J,hmem⟩⟩
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
      (∀ q : Fin 6, SensitivityLabelCache12607.SensitivityQ.DefectBound T label q.val
        (cutoff q)) ∧
      (∀ I : Finset (Fin k), ∀ m : Fin k → Fin 2, HasSource T I →
        (∀ i ∈ I, (I.filter (fun j => T.Adj i j ∧ label i j ≠ m j)).card ≤ 0) →
          I.card < 22) := by
  obtain ⟨a,ha⟩ := exists_avoiding_below T hodd hdlo hdhi hout
  exact labeling_of_avoiding T a ha







/-- One checked upper budget covers every smaller regular odd tournament. -/
theorem shared_labeling_source_below_14055_q5_lll {k d : ℕ}
    (hodd : k = 2*d+1) (hdlo : 21 ≤ d) (hdhi : d ≤ 7027)
    (A : Fin k → Fin k → Prop)
    (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i))
    (hout : ∀ i, (Finset.univ.filter (A i)).card = d) :
    ∃ label : Fin k → Fin k → Fin 2,
      (∀ q : Fin 6, ∀ I : Finset (Fin k), ∀ colors : Fin k → Fin 2,
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ q.val) →
          I.card < (![24,31,38,44,50,55] q)) ∧
      (∀ I : Finset (Fin k), ∀ colors : Fin k → Fin 2,
        (∃ s ∈ I, ∀ j ∈ I, j ≠ s → A s j) →
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ 0) →
          I.card < 22) := by
  let T : Tournament k := { Adj := A, loopless := hloop, edge_compl := hcomp }
  obtain ⟨label,hdefect,hsource⟩ := labeling_exists_below T hodd hdlo hdhi hout
  exact ⟨label,hdefect,hsource⟩








end
end SensitivitySourceLabeling14055Q5
end


set_option autoImplicit false
open scoped Classical

namespace CycleGraph

def adj (d : ℕ) (i j : Fin (2*d+1)) : Prop :=
  0 < (j-i).val ∧ (j-i).val ≤ d

theorem loopless (d : ℕ) (i : Fin (2*d+1)) : ¬ adj d i i := by
  simp [adj]

theorem complement (d : ℕ) {i j : Fin (2*d+1)} (hij : i ≠ j) :
    adj d i j ↔ ¬ adj d j i := by
  have hδ : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
  have hp : 0 < (j-i).val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hδ)
  have hb := (j-i).isLt
  have hn : (i-j).val = 2*d+1-(j-i).val := by
    rw [← neg_sub j i, Fin.val_neg, if_neg hδ]
  change (0 < (j-i).val ∧ (j-i).val ≤ d) ↔
    ¬ (0 < (i-j).val ∧ (i-j).val ≤ d)
  rw [hn]
  omega

theorem outdegree (d : ℕ) (i : Fin (2*d+1)) :
    (Finset.univ.filter (adj d i)).card = d := by
  let z : Fin (2*d+1) := 0
  let b : Fin (2*d+1) := ⟨d, by omega⟩
  have he : (Finset.Ioc z b).card =
      (Finset.univ.filter (adj d i)).card :=
    Finset.card_equiv (Equiv.addLeft i) (by
      intro x
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_univ, true_and]
      change (0 < x.val ∧ x.val ≤ d) ↔
        (0 < ((i+x)-i).val ∧ ((i+x)-i).val ≤ d)
      rw [add_sub_cancel_left])
  rw [← he, Fin.card_Ioc]
  change d - 0 = d
  exact Nat.sub_zero d

end CycleGraph

set_option autoImplicit false
open scoped Classical

def fixedCutoffs : Fin 6 → ℕ := ![24, 31, 38, 44, 50, 55]

theorem fixedLabeling_exists :
    ∃ label : Fin 14055 → Fin 14055 → Fin 2,
      (∀ (I : Finset (Fin 14055)) (colors : Fin 14055 → Fin 2),
        (∀ i ∈ I, ∀ j ∈ I, CycleGraph.adj 7027 i j → label i j = colors j) →
          I.card < 24) ∧
      (∀ q : Fin 6, ∀ (I : Finset (Fin 14055)) (colors : Fin 14055 → Fin 2),
        (∀ i ∈ I, (I.filter (fun j =>
          CycleGraph.adj 7027 i j ∧ label i j ≠ colors j)).card ≤ q.val) →
            I.card < fixedCutoffs q) ∧
      (∀ (I : Finset (Fin 14055)) (colors : Fin 14055 → Fin 2),
        (∃ s ∈ I, ∀ j ∈ I, j ≠ s → CycleGraph.adj 7027 s j) →
        (∀ i ∈ I, (I.filter (fun j =>
          CycleGraph.adj 7027 i j ∧ label i j ≠ colors j)).card ≤ 0) →
            I.card < 22) := by
  obtain ⟨label, hdefect, hsource⟩ :=
    SensitivitySourceLabeling14055Q5.shared_labeling_source_below_14055_q5_lll
      (k := 14055) (d := 7027) rfl (by decide) (by decide)
      (CycleGraph.adj 7027) (CycleGraph.loopless 7027)
      (fun {_ _} h => CycleGraph.complement 7027 h) (CycleGraph.outdegree 7027)
  refine ⟨label, ?_, hdefect, hsource⟩
  intro I colors hcoherent
  apply hdefect 0 I colors
  intro i hi
  apply Nat.le_zero.mpr
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro j hj hbad
  exact hbad.2 (hcoherent i hi j hj hbad.1)

end ProfileLabelingCache


set_option autoImplicit false
namespace SensitivityProfileSearch
open SensitivityProfileCycle

theorem envelope_witness {n : ℕ} (A : Matrix n) (i j : Fin n) (hij : i ≤ j) :
    ∃ a b, i ≤ a ∧ a ≤ b ∧ b ≤ j ∧ A a b = envelope A i j := by
  obtain ⟨ab, hab, heq⟩ :=
    Finset.exists_mem_eq_inf' (intervals_nonempty hij) (fun ab => A ab.1 ab.2)
  have hm : i ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ j := by
    simpa only [intervals, Finset.mem_filter, Finset.mem_univ, true_and] using hab
  exact ⟨ab.1, ab.2, hm.1, hm.2.1, hm.2.2, by simp [envelope, hij, heq]⟩

theorem envelope_le {n : ℕ} (A : Matrix n) {i j a b : Fin n}
    (hia : i ≤ a) (hab : a ≤ b) (hbj : b ≤ j) : envelope A i j ≤ A a b := by
  rw [envelope, dif_pos (hia.trans (hab.trans hbj))]
  exact Finset.inf'_le (fun ab : Fin n × Fin n => A ab.1 ab.2)
    (b := (a,b)) (by simp [intervals, hia, hab, hbj])

theorem envelope_nested {n : ℕ} (A : Matrix n) {i j a b : Fin n}
    (hia : i ≤ a) (hab : a ≤ b) (hbj : b ≤ j) :
    envelope A i j ≤ envelope A a b := by
  obtain ⟨c, d, hac, hcd, hdb, heq⟩ := envelope_witness A a b hab
  rw [← heq]
  exact envelope_le A (hia.trans hac) hcd (hdb.trans hbj)

theorem normalize_positive {n : ℕ} {P : Profile n} (hP : PositiveUpper P) :
    PositiveUpper (normalize P) := by
  intro i j hij
  obtain ⟨a,b,_,hab,_,hz⟩ := envelope_witness P.zero i j hij
  obtain ⟨c,d,_,hcd,_,hy⟩ := envelope_witness P.one i j hij
  exact ⟨by simpa only [normalize, ← hz] using (hP a b hab).1,
    by simpa only [normalize, ← hy] using (hP c d hcd).2⟩

theorem orbit_nested {n p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (P : Profile n) (d : ℕ) {i j a b : Fin n}
    (hia : i ≤ a) (hab : a ≤ b) (hbj : b ≤ j) :
    (orbit recipes P d).zero i j ≤ (orbit recipes P d).zero a b ∧
    (orbit recipes P d).one i j ≤ (orbit recipes P d).one a b := by
  cases d with
  | zero => exact ⟨envelope_nested _ hia hab hbj, envelope_nested _ hia hab hbj⟩
  | succ d => exact ⟨envelope_nested _ hia hab hbj, envelope_nested _ hia hab hbj⟩

theorem orbit_compatible {n p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (P : Profile n) (d : ℕ) (C : Recipe n) (hC : C.Valid) :
    Compatible C (orbit recipes P d).zero (orbit recipes P d).one := by
  intro i j hij hi
  have hg := hC.2.2 i j hij hi
  have ht := hC.1 hij
  constructor
  · exact (orbit_nested recipes P d (hg.1.trans hg.2.2) ht le_rfl).1
  · exact (orbit_nested recipes P d le_rfl hg.1 (hg.2.2.trans ht)).2

theorem periodicRecipe_at {n p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (d : Fin (p+1)) : periodicRecipe recipes d.val = recipes d := by
  unfold periodicRecipe
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt d.isLt)

theorem orbit_step_zero {n p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (P : Profile n) (d : Fin (p+1)) (i j : Fin n) (hij : i ≤ j) :
    ∃ a b, i ≤ a ∧ a ≤ b ∧ b ≤ j ∧
      rawZeroSourceCombined 14055 24 (extendCutoffs cutoffs) 22
        (recipes d) (orbit recipes P d.val).zero (orbit recipes P d.val).one a b ≤
          (orbit recipes P (d.val+1)).zero i j := by
  rw [orbit, periodicRecipe_at]
  obtain ⟨a,b,hia,hab,hbj,heq⟩ := envelope_witness
    (rawZeroSourceCombined 14055 24 (extendCutoffs cutoffs) 22
      (recipes d) (orbit recipes P d.val).zero (orbit recipes P d.val).one) i j hij
  exact ⟨a,b,hia,hab,hbj,le_of_eq heq⟩

theorem orbit_step_one {n p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (P : Profile n) (d : Fin (p+1)) (i j : Fin n) (hij : i ≤ j) :
    ∃ a b, i ≤ a ∧ a ≤ b ∧ b ≤ j ∧
      rawOne 7027 (recipes d) (orbit recipes P d.val).zero
        (orbit recipes P d.val).one a b ≤ (orbit recipes P (d.val+1)).one i j := by
  rw [orbit, periodicRecipe_at]
  obtain ⟨a,b,hia,hab,hbj,heq⟩ := envelope_witness
    (rawOne 7027 (recipes d) (orbit recipes P d.val).zero
      (orbit recipes P d.val).one) i j hij
  exact ⟨a,b,hia,hab,hbj,le_of_eq heq⟩

end SensitivityProfileSearch

namespace SensitivityProfileSearch
open SensitivityProfileCycle

theorem certificate_of_return (n p radius : ℕ)
    (recipes : Fin (p+1) → Recipe (n+1)) (initial : Profile (n+1))
    (hr : 1 < radius) (hgap : radius^43 < (14055^(p+1))^20)
    (hpositive : PositiveUpper initial)
    (hrecipes : ∀ d, (recipes d).Valid ∧
      ∀ i, 3 ≤ i.val → 0 < (recipes d).tol i → (recipes d).tol i < 6)
    (hreturn : ReturnsWithin recipes initial radius) :
    ∃ c : Certificate, 1 < c.radius ∧
      c.radius^43 < (c.vertices^c.period)^20 := by
  classical
  obtain ⟨label, hcoherent, hdefect, hsource⟩ := ProfileLabelingCache.fixedLabeling_exists
  let c : Certificate := {
    states := n+1
    output := 0
    vertices := 14055
    vertices_gt_one := by decide
    degree := 7027
    period := p+1
    period_pos := Nat.zero_lt_succ p
    radius := radius
    ordinaryCutoff := 24
    ordinary_ge_four := by decide
    sourceCutoff := 22
    source_ge_four := by decide
    toleranceCount := 6
    cutoffs := cutoffs
    cutoff_zero := rfl
    adj := ProfileLabelingCache.CycleGraph.adj 7027
    loopless := ProfileLabelingCache.CycleGraph.loopless 7027
    complement := fun {_ _} hij => ProfileLabelingCache.CycleGraph.complement 7027 hij
    outdegree := ProfileLabelingCache.CycleGraph.outdegree 7027
    label := label
    coherent := hcoherent
    defect := hdefect
    source := hsource
    recipe := recipes
    valid := fun d => (hrecipes d).1
    tolerance_bound := fun d => (hrecipes d).2
    zeroProfile := fun d => (orbit recipes initial d.val).zero
    oneProfile := fun d => (orbit recipes initial d.val).one
    initial_positive := normalize_positive hpositive
    compatible := fun d => orbit_compatible recipes initial d.val (recipes d) (hrecipes d).1
    zero_step := fun d i j hij => orbit_step_zero recipes initial d i j hij
    one_step := fun d i j hij => orbit_step_one recipes initial d i j hij
    zero_cycle := fun i j hij => (hreturn i j hij).1
    one_cycle := fun i j hij => (hreturn i j hij).2
  }
  exact ⟨c, hr, hgap⟩

end SensitivityProfileSearch


theorem solution :
    ∃ c : SensitivityProfileCycle.Certificate,
      1 < c.radius ∧ c.radius ^ 43 < (c.vertices ^ c.period) ^ 20 := by
  obtain ⟨n,p,radius,recipes,initial,hr,hgap,hpositive,hrecipes,hreturn⟩ :=
    SensitivityProfileSearch.exists_215_orbit
  exact SensitivityProfileSearch.certificate_of_return
    n p radius recipes initial hr hgap hpositive hrecipes hreturn

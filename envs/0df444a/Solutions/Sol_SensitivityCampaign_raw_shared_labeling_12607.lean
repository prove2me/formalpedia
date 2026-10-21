-- Prove2me | solution 1 for SensitivityCampaign.raw_shared_labeling_12607
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-20T06:33:05.771225+00:00
-- url     : https://prove2.me/submissions/8af4bba2-06b1-4dfd-b9bc-e1374a2578ea

import Mathlib

/-!
A shared binary labeling for any tournament on 12,607 vertices, with simultaneous
q-defect thresholds 23,33,45,57,71. The proof uses exact finite cylinder counts,
an asymmetric finite local lemma, typewise dependency bounds, and the closed
rational gamma=254/253 certificate. It contains no Boolean-family construction
or campaign theorem import. Retained proof declarations come from the checked
four-phase seed bundle; pruning and component hashes are in the manifest.
-/
set_option autoImplicit false
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

def eventBad {k Q : ℕ} (T : Tournament k) (s : Fin (Q+1) → ℕ)
    (i : EventIndex k Q s) : Finset (EdgeAssignment k) := localBad T i.1.val i.2.1

def neighbors {k Q : ℕ} (s : Fin (Q+1) → ℕ)
    (i : EventIndex k Q s) : Finset (EventIndex k Q s) :=
  Finset.univ.filter fun j => 2 ≤ (i.2.1 ∩ j.2.1).card

theorem event_card_bound {k Q : ℕ} (T : Tournament k) (s : Fin (Q+1) → ℕ)
    (i : EventIndex k Q s) :
    ((eventBad T s i).card : ℚ) ≤
      eventProbability i.1.val (s i.1) * Fintype.card (EdgeAssignment k) := by
  have hs : i.2.1.card = s i.1 := (Finset.mem_powersetCard.mp i.2.2).2
  simpa only [eventBad,hs] using localBad_probability_bound T i.1.val i.2.1

theorem event_away {k Q : ℕ} (T : Tournament k) (s : Fin (Q+1) → ℕ)
    (i : EventIndex k Q s) (S : Finset (EventIndex k Q s))
    (hi : i ∉ S) (hS : ∀ j ∈ S, j ∉ neighbors s i) :
    ((eventBad T s i ∩ SensitivityLLL.avoid (eventBad T s) S).card : ℚ) ≤
      eventProbability i.1.val (s i.1) *
        ((SensitivityLLL.avoid (eventBad T s) S).card : ℚ) := by
  let C : Finset (Fin k × Fin k) := T.internalEdges i.2.1
  let E : Finset (EdgeAssignment k) := eventBad T s i
  let F : Finset (EdgeAssignment k) := SensitivityLLL.avoid (eventBad T s) S
  have hE : DependsOn (ι := Fin k × Fin k) (β := Fin 2) E C :=
    localBad_depends T i.1.val i.2.1
  have hDis : ∀ j ∈ S, Disjoint C (T.internalEdges j.2.1) := by
    intro j hj
    have hh := hS j hj
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    have hcard : (i.2.1 ∩ j.2.1).card ≤ 1 := by omega
    exact internalEdges_disjoint T i.2.1 j.2.1 hcard
  have hF : ∀ a b : EdgeAssignment k,
      (∀ ij, ij ∉ C → a ij = b ij) → (a ∈ F ↔ b ∈ F) := by
    intro a b hab
    have hlocal (j : EventIndex k Q s) (hj : j ∈ S) :
        a ∈ eventBad T s j ↔ b ∈ eventBad T s j :=
      localBad_depends T j.1.val j.2.1 a b (fun ij hij =>
        hab ij (fun hc => Finset.disjoint_left.mp (hDis j hj) hc hij))
    change a ∈ SensitivityLLL.avoid (eventBad T s) S ↔
      b ∈ SensitivityLLL.avoid (eventBad T s) S
    rw [SensitivityLLL.mem_avoid, SensitivityLLL.mem_avoid]
    constructor
    · intro ha j hj hb
      exact ha j hj ((hlocal j hj).mpr hb)
    · intro hb j hj ha
      exact hb j hj ((hlocal j hj).mp ha)
  have hp : (E.card : ℚ) ≤ eventProbability i.1.val (s i.1) * (2 : ℚ)^(k*k) := by
    have h := event_card_bound T s i
    simpa only [E, EdgeAssignment, Fintype.card_fun, Fintype.card_prod,
      Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h
  exact bound_inter_card_outside (ι := Fin k × Fin k) (β := Fin 2) C E F
    (eventProbability i.1.val (s i.1)) hE hF (by
      simpa only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
        Nat.cast_pow, Nat.cast_ofNat] using hp)

/-- A shared LLL labeling gives the same contract as the existing union-bound
labeling theorem. The only inputs here are the explicit finite LLL inequalities. -/
theorem labeling_exists_lll {k Q : ℕ} (T : Tournament k) (s : Fin (Q+1) → ℕ)
    (x : EventIndex k Q s → ℚ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, eventProbability i.1.val (s i.1) ≤
      x i * ∏ j ∈ neighbors s i, (1-x j)) :
    ∃ L : Labeling T 2 (s 0),
      ∀ q : Fin (Q+1), SensitivityQ.DefectBound T L.label q.val (s q) := by
  obtain ⟨a,ha⟩ := SensitivityLLL.asymmetric_local_lemma (eventBad T s)
    (fun i => eventProbability i.1.val (s i.1)) x (neighbors s) hx0 hx1 hp (event_away T s)
  have hdefect (q : Fin (Q+1)) : SensitivityQ.DefectBound T (fun i j => a (i,j)) q.val (s q) := by
    intro I m hout
    by_contra hI
    obtain ⟨J,hJI,hJ⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hI)
    have houtJ : ∀ i ∈ J, (J.filter fun j => T.Adj i j ∧ a (i,j) ≠ m j).card ≤ q.val := by
      intro i hi
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hJI)).trans (hout i (hJI hi))
    let j : EventIndex k Q s := ⟨q,⟨J,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hJ⟩⟩⟩
    apply ha j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,m,houtJ⟩
  refine ⟨⟨(fun i j => a (i,j)), ?_⟩,hdefect⟩
  intro I m hcoh
  apply hdefect 0 I m
  intro i hi
  have he : (I.filter fun j => T.Adj i j ∧ a (i,j) ≠ m j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hj,hij,hne⟩ := Finset.mem_filter.mp hj
    exact hne (hcoh i hi j hj hij)
  rw [he]
  exact Nat.zero_le _

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

/-- The same bound when b-subsets are a subtype, as in the q-fiber of the
sigma event index `(q, B)` for the asymmetric Lovasz local lemma. -/
theorem card_overlap_two_subtype_le (k : ℕ) (A : Finset (Fin k))
    (b : ℕ) (hb : 2 ≤ b) :
    ((Finset.univ : Finset
      (((Finset.univ : Finset (Fin k)).powersetCard b) : Type)).filter
      fun B => 2 ≤ (A ∩ B.1).card).card ≤
      A.card.choose 2 * (k - 2).choose (b - 2) := by
  classical
  apply Nat.le_trans ?_ (card_overlap_two_fin_le k A b hb)
  apply Finset.card_le_card_of_injOn (fun B => B.1)
  · intro B hB
    exact Finset.mem_filter.mpr ⟨B.2, (Finset.mem_filter.mp hB).2⟩
  · intro B _ C _ hBC
    exact Subtype.ext hBC

/-- The bound for each tolerance-type fiber of the full sigma event index.
This preserves the per-type neighbor counts needed to factor the asymmetric
LLL product; a bound only on the total degree would not suffice there. -/
theorem card_overlap_two_sigma_fiber_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (s : ι → ℕ) (A : Finset (Fin k)) (q : ι) (hb : 2 ≤ s q) :
    ((Finset.univ : Finset (Σ p : ι,
      (((Finset.univ : Finset (Fin k)).powersetCard (s p)) : Type))).filter
      fun j => j.1 = q ∧ 2 ≤ (A ∩ j.2.1).card).card ≤
      A.card.choose 2 * (k - 2).choose (s q - 2) := by
  classical
  apply Nat.le_trans ?_ (card_overlap_two_fin_le k A (s q) hb)
  apply Finset.card_le_card_of_injOn (fun j => j.2.1)
  · intro j hj
    have hjq : j.1 = q := (Finset.mem_filter.mp hj).2.1
    have hmem : j.2.1 ∈ (Finset.univ : Finset (Fin k)).powersetCard (s q) := by
      simpa only [hjq] using j.2.2
    exact Finset.mem_filter.mpr ⟨hmem, (Finset.mem_filter.mp hj).2.2⟩
  · intro j hj j' hj' hBB
    rcases j with ⟨p, B⟩
    rcases j' with ⟨p', B'⟩
    have hp : p = q := (Finset.mem_filter.mp hj).2.1
    have hp' : p' = q := (Finset.mem_filter.mp hj').2.1
    subst p
    subst p'
    have hB : B = B' := Subtype.ext hBB
    subst B'
    rfl

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

/- Pruned labeling component: GammaArithmetic12607 -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 4096
open scoped BigOperators

namespace SensitivityLLL12607
noncomputable section

def thresholds : Fin 5 → ℕ := ![23,33,45,57,71]
def coefficient : Fin 5 → ℕ :=
  ![2487806756060194537136164257449507151511966340166581617828772242975,
    1533813186338333949202480785934383205957215674032773663801707701899298912136864216111353470800,
    3243760359373316974504911080351412449596574190252502234289734338391685519453920417373471126104625694768964485925688774218950,
    237103375473493671046664068262485048360074429657330270055464334718638978672916642476505385343228818447499759056804939598070845853808171515934202817290716,
    41992662969923664048094680788416158617134257650596746046851150363373464456861005489545525205660191668249477520092561557993018716332381822814849482296872947323518771678527590167762601100]
def tags (q : Fin 5) : ℕ := 2^(thresholds q)*(thresholds q)^(q.val*thresholds q)
def degree (q : Fin 5) : ℕ := (thresholds q).choose 2

theorem coefficient_exact (q : Fin 5) :
    (12607-2).choose (thresholds q-2) = coefficient q := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  fin_cases q <;> decide

theorem integer_budget :
    254 * (∑ q : Fin 5, coefficient q * tags q * 127^(degree q) *
      253^(2485-degree q)) ≤ 253^2485 := by
  decide


theorem reduced_activity_budget :
    ∑ q : Fin 5, (coefficient q : ℚ) *
      ((tags q : ℚ) * ((127 : ℚ)/253)^(degree q)) ≤ 1 - (253 : ℚ)/254 := by
  exact SensitivityLLL.rational_power_budget coefficient tags degree
    2485 127 253 254 (by decide) (by decide)
    (by intro q; fin_cases q <;> decide) integer_budget (by decide)

end
end SensitivityLLL12607

/- Pruned labeling component: GammaLabelGeneric -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
open OAI.Paper320 Sensitivity205
open scoped Classical BigOperators

namespace SensitivityQLLL
noncomputable section

/-- One scalar rational budget supplies a simultaneous small-defect labeling
for an arbitrary tournament. No independence between overlapping events is
assumed: the degree bound retains a separate count for every tolerance type. -/
theorem labeling_exists_gamma {k Q : ℕ} (T : Tournament k)
    (s : Fin (Q+1) → ℕ) (γ : ℚ) (hγ : 1 < γ)
    (hs0 : ∀ q, 2 ≤ s q) (hsk : ∀ q, s q ≤ k)
    (hbudget : ∑ q : Fin (Q+1),
      (((k-2).choose (s q-2) : ℕ) : ℚ) *
        (eventProbability q.val (s q) * γ ^ (s q).choose 2) ≤ 1 - 1 / γ) :
    ∃ L : Labeling T 2 (s 0),
      ∀ q : Fin (Q+1), SensitivityQ.DefectBound T L.label q.val (s q) := by
  let p : Fin (Q+1) → ℚ := fun q => eventProbability q.val (s q)
  let u : Fin (Q+1) → ℕ := fun q => (s q).choose 2
  let C : Fin (Q+1) → ℕ := fun q => (k-2).choose (s q-2)
  let x : Fin (Q+1) → ℚ := fun q => p q * γ ^ u q
  have hp0 (q : Fin (Q+1)) : 0 ≤ p q := by
    dsimp [p, eventProbability]
    positivity
  have hx0 (q : Fin (Q+1)) : 0 ≤ x q :=
    mul_nonneg (hp0 q) (pow_nonneg (by linarith : (0 : ℚ) ≤ γ) _)
  have hC (q : Fin (Q+1)) : 1 ≤ C q := by
    exact Nat.choose_pos (Nat.sub_le_sub_right (hsk q) 2)
  have hx1 : ∀ q, x q < 1 :=
    SensitivityLLL.activity_lt_one_of_budget x C γ hγ hx0 hC hbudget
  apply labeling_exists_lll T s (fun i => x i.1)
    (fun i => hx0 i.1) (fun i => hx1 i.1)
  intro i
  have hcard : i.2.1.card = s i.1 := (Finset.mem_powersetCard.mp i.2.2).2
  have hcount (q : Fin (Q+1)) :
      ((neighbors s i).filter fun j => j.1 = q).card ≤ u i.1 * C q := by
    have hb :
        (((Finset.univ : Finset (Fin k)).powersetCard (s q)).filter
          fun B => 2 ≤ (i.2.1 ∩ B).card).card ≤ u i.1 * C q := by
      simpa only [hcard, u, C] using
        SensitivityLLL.card_overlap_two_fin_le k i.2.1 (s q) (hs0 q)
    apply Nat.le_trans ?_ hb
    apply Finset.card_le_card_of_injOn (fun j : EventIndex k Q s => j.2.1)
    · intro j hj
      have hjq : j.1 = q := (Finset.mem_filter.mp hj).2
      have hmem : j.2.1 ∈ (Finset.univ : Finset (Fin k)).powersetCard (s q) := by
        simpa only [hjq] using j.2.2
      have hov : 2 ≤ (i.2.1 ∩ j.2.1).card :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      exact Finset.mem_filter.mpr ⟨hmem, hov⟩
    · intro j hj j' hj' hBB
      rcases j with ⟨p, B⟩
      rcases j' with ⟨p', B'⟩
      have hp : p = q := (Finset.mem_filter.mp hj).2
      have hp' : p' = q := (Finset.mem_filter.mp hj').2
      subst p
      subst p'
      have hB : B = B' := Subtype.ext hBB
      subst B'
      rfl

  exact SensitivityLLL.rank_one_activity_condition (neighbors s i)
    (fun j => j.1) p u C i.1 γ hγ hp0 hx1 hcount hbudget

/-- Cancel the binary edge denominator against an even gamma numerator
before checking the closed integer certificate. -/
theorem event_activity_double (q s a d : ℕ) (hd : 0 < d) :
    eventProbability q s * (((2*a : ℕ) : ℚ) / d) ^ s.choose 2 =
      ((2^s*s^(q*s) : ℕ) : ℚ) * ((a : ℚ) / d) ^ s.choose 2 := by
  unfold eventProbability
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_pow, mul_pow, div_pow]
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp [hd0]
  <;> ring

end
end SensitivityQLLL

/- Pruned labeling component: GammaLabel12607 -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 4096
open OAI.Paper320 Sensitivity205
open scoped Classical BigOperators

namespace SensitivityLLL12607
noncomputable section

theorem activity_budget :
    ∑ q : Fin 5, (((12607-2).choose (thresholds q-2) : ℕ) : ℚ) *
      (SensitivityQLLL.eventProbability q.val (thresholds q) *
        ((254 : ℚ)/253)^((thresholds q).choose 2)) ≤
      1 - 1/((254 : ℚ)/253) := by
  have hactivity (q : Fin 5) :
      SensitivityQLLL.eventProbability q.val (thresholds q) *
        ((254 : ℚ)/253)^((thresholds q).choose 2) =
        (tags q : ℚ) * ((127 : ℚ)/253)^(degree q) := by
    simpa only [tags, degree, show (2*127 : ℕ) = 254 by decide, Nat.cast_ofNat] using
      SensitivityQLLL.event_activity_double q.val (thresholds q) 127 253 (by decide)
  simp_rw [coefficient_exact, hactivity]
  convert reduced_activity_budget using 1 <;> norm_num

/-- One actual edge-labeling simultaneously forbids every tolerance type
used by the four-stage construction. -/
theorem labeling_exists (T : Tournament 12607) :
    ∃ L : Labeling T 2 23,
      ∀ a : Fin 5, SensitivityQ.DefectBound T L.label a.val
        (![23,33,45,57,71] a) := by
  exact SensitivityQLLL.labeling_exists_gamma T thresholds ((254 : ℚ)/253)
    (by norm_num) (by intro q; fin_cases q <;> decide)
    (by intro q; fin_cases q <;> decide) activity_budget

end
end SensitivityLLL12607

end SensitivityLabelCache12607

/-- One actual raw binary labeling simultaneously excludes every listed defect type. -/
theorem solution (A : Fin 12607 → Fin 12607 → Prop)
    (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i)) :
    ∃ label : Fin 12607 → Fin 12607 → Fin 2,
      ∀ q : Fin 5, ∀ I : Finset (Fin 12607),
        ∀ colors : Fin 12607 → Fin 2,
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ q.val) →
          I.card < (![23,33,45,57,71] q) := by
  let T : SensitivityLabelCache12607.OAI.Paper320.Tournament 12607 := {
    Adj := A
    loopless := hloop
    edge_compl := hcomp }
  obtain ⟨L,hL⟩ := SensitivityLabelCache12607.SensitivityLLL12607.labeling_exists T
  refine ⟨L.label, ?_⟩
  simpa only [SensitivityLabelCache12607.SensitivityQ.DefectBound, T] using hL

#print axioms solution

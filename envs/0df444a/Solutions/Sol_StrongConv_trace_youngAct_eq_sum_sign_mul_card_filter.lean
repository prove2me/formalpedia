-- Prove2me | solution 1 for StrongConv.trace_youngAct_eq_sum_sign_mul_card_filter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:15:24.778272+00:00
-- url     : https://prove2.me/submissions/70889247-9162-4ec8-a674-f64de1835617

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Theorems.Thm_StrongConv_exists_linearEquiv_youngSpace_specht
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Theorems.Thm_OAI_Saxl_specht_irreducible
universe uX uV uW

section
/-!
# `youngSpace N (stableRows μ N)` as the Specht module of the partition `μ[N]`
-/

namespace HananyPuder.W2HP.PartB

open StrongConv OAI.Saxl

noncomputable section

/-- The representation of `S_N` on `youngSpace N rows`. -/
def youngRep (N : ℕ) (rows : List ℕ) :
    Representation ℂ (Equiv.Perm (Fin N)) (youngSpace N rows) where
  toFun σ := youngAct N rows σ
  map_one' := by
    ext x
    simp [youngAct]
  map_mul' σ τ := by
    ext x
    simp [youngAct, mul_assoc]

lemma youngEquivOfEq_aux {N : ℕ} :
    ∀ (c c' : MonoidAlgebra ℂ (Equiv.Perm (Fin N))) (_hc : c = c')
      (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin N)) V)
      (F : MonoidAlgebra ℂ (Equiv.Perm (Fin N)) → Type) [∀ c, AddCommGroup (F c)]
      [∀ c, Module ℂ (F c)] (R : ∀ c, Representation ℂ (Equiv.Perm (Fin N)) (F c)),
      Nonempty (ρ.Equiv (R c)) → Nonempty (ρ.Equiv (R c')) := by
  rintro c _ rfl V _ _ ρ F _ _ R h
  exact h

/-- Lists with the same Young symmetrizer give equivalent representations. -/
lemma youngEquivOfEq {N : ℕ} {L L' : List ℕ} (h : youngSymmetrizer N L = youngSymmetrizer N L') :
    Nonempty ((youngRep N L).Equiv (youngRep N L')) := by
  let F : MonoidAlgebra ℂ (Equiv.Perm (Fin N)) → Type := fun c =>
    (Submodule.span (MonoidAlgebra ℂ (Equiv.Perm (Fin N))) {c}).restrictScalars ℂ
  let R : ∀ c, Representation ℂ (Equiv.Perm (Fin N)) (F c) := fun c =>
    { toFun := fun σ => (LinearMap.mulLeft ℂ (MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) σ)).restrict
        (fun x hx => by
          rw [Submodule.restrictScalars_mem] at hx ⊢
          exact (Submodule.span _ {c}).smul_mem _ hx)
      map_one' := by ext x; simp
      map_mul' := fun σ τ => by ext x; simp [mul_assoc] }
  exact youngEquivOfEq_aux (youngSymmetrizer N L) (youngSymmetrizer N L') h _ (youngRep N L) F R
    ⟨Representation.Equiv.refl _⟩

end

end HananyPuder.W2HP.PartB
end

section
/-!
# Shape rigidity of Specht modules and orthonormality of their characters

Ported (credited) from openai/math `lean/OAI/RepresentationTheory/Saxl/{Basic,Polytabloid,
SpechtSubmodule,ShapeRigidity,SpechtClassification}.lean`: Specht modules of different shapes
are inequivalent (James, *The representation theory of the symmetric groups*, Thm 4.12), hence the
characters of the Specht modules of the partitions of `n` are orthonormal.
-/

namespace HananyPuder.W2HP.PartR

open OAI OAI.Saxl

noncomputable section


theorem column_perm_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : columnGroup t) (hg : rowWord t ∘ (g : Equiv.Perm (Fin n)) = rowWord t) :
    g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Fin.val (congrFun hg i)
  · exact g.property i

theorem polytabloid_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t (rowWord t) = 1 := by
  classical
  unfold polytabloid
  simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  rw [Finset.sum_eq_single (1 : columnGroup t)]
  · simp
  · intro b hb hb1
    have hn : rowWord t ∘ (b : Equiv.Perm (Fin n)) ≠ rowWord t :=
      fun h => hb1 (column_perm_rowWord t b h)
    simp [hn]
  · simp

lemma columnAlt_row {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (Pi.single (rowWord t) 1) = polytabloid t := by
  simp [columnAlt, polytabloid, LinearMap.sum_apply]

lemma tableau_image {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Finset.univ.image (fun i : Fin n => (t i).val) = μ.cells := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact (t i).property
  · intro hx; exact ⟨t.symm ⟨x, hx⟩, by simp⟩

lemma rowLen_eq_count {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (r : ℕ) :
    μ.rowLen r = (Finset.univ.filter (fun i => (t i).val.1 = r)).card := by
  classical
  rw [YoungDiagram.rowLen_eq_card]
  have hf : μ.row r = (Finset.univ.filter (fun i => (t i).val.1 = r)).image
      (fun i => (t i).val) := by
    unfold YoungDiagram.row
    conv_lhs => rw [← tableau_image t]
    rw [Finset.filter_image]
  rw [hf, Finset.card_image_iff.mpr]
  intro i hi j hj h
  exact t.injective (Subtype.val_injective h)

end

end HananyPuder.W2HP.PartR
end

section
open StrongConv OAI.Saxl
namespace StrongConvW2HP.Q289
noncomputable section
/-!
# q289 Blueprint: James, Theorem 19.2 (determinantal form), by the norm argument

Notation: `ℓ = rows.length`, `α_w i = rows_i - i + w i` for `w ∈ S_ℓ`,
`ξ_α σ` = number of `σ`-fixed words `f : Fin N → Fin ℓ` of content `α`,
`ψ = ∑_w sgn w · ξ_{α_w}`, `χ σ = trace (youngAct N rows σ)`.

Route (Macdonald I.7 / Fulton–Harris §4 style, with James's dominance lemma):
* `∑_σ ψ σ ^ 2 = N!`        (Burnside: `∑_σ ξ_α ξ_β = N! · #tables(α, β)`; then the
                               alternant identity for tables, i.e. Cauchy's identity);
* `∑_σ χ σ χ σ⁻¹ = N!`       (irreducibility of the Specht module);
* `∑_σ ψ σ χ σ⁻¹ = N! · m`, `m ≥ 1`  (`∑_σ ξ_α χ(σ⁻¹) = N! dim Hom(S^μ, M^α)`; James's
                               dominance lemma kills `w ≠ 1`; `S^μ ⊆ M^μ` gives `m ≥ 1`);
* `χ` real and `χ σ⁻¹ = χ σ`; so `∑ (ψ - m χ)^2 = N!(1 - m²) ≤ 0`, whence `χ = ψ`.
-/
/-- `ξ_α σ`: the number of `σ`-fixed words of content `α`. -/
def xi {N ℓ : ℕ} (α : Fin ℓ → ℤ) (σ : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun f : Fin N → Fin ℓ =>
    (∀ x, f (σ x) = f x) ∧
      ∀ i, ((Finset.univ.filter fun x => f x = i).card : ℤ) = α i).card

/-- `α_w i = rows_i - i + w i`. -/
def alphaW (rows : List ℕ) (w : Equiv.Perm (Fin rows.length)) : Fin rows.length → ℤ :=
  fun i => (rows.get i : ℤ) - (i : ℕ) + (w i : ℕ)

/-- `ψ = ∑_w sgn w · ξ_{α_w}`. -/
def psi (N : ℕ) (rows : List ℕ) (σ : Equiv.Perm (Fin N)) : ℤ :=
  ∑ w : Equiv.Perm (Fin rows.length), (Equiv.Perm.sign w : ℤ) * (xi (alphaW rows w) σ : ℤ)

/-- The number of `ℓ × ℓ` matrices of naturals `≤ N` with row sums `α` and column sums `β`. -/
def tables (N ℓ : ℕ) (α β : Fin ℓ → ℤ) : ℕ :=
  (Finset.univ.filter fun M : Fin ℓ → Fin ℓ → Fin (N + 1) =>
    (∀ i, ((∑ j, (M i j : ℕ) : ℕ) : ℤ) = α i) ∧ ∀ j, ((∑ i, (M i j : ℕ) : ℕ) : ℤ) = β j).card

/-- Words of content `α`. -/
def Words (N ℓ : ℕ) (α : Fin ℓ → ℤ) : Type :=
  {f : Fin N → Fin ℓ // ∀ i, ((Finset.univ.filter fun x => f x = i).card : ℤ) = α i}

instance (N ℓ : ℕ) (α : Fin ℓ → ℤ) : Fintype (Words N ℓ α) := by
  unfold Words; classical infer_instance

instance (N ℓ : ℕ) (α : Fin ℓ → ℤ) : DecidableEq (Words N ℓ α) := by
  unfold Words; classical infer_instance

lemma card_filter_comp {N ℓ : ℕ} (f : Fin N → Fin ℓ) (σ : Equiv.Perm (Fin N)) (i : Fin ℓ) :
    (Finset.univ.filter fun x => f (σ x) = i).card = (Finset.univ.filter fun x => f x = i).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp σ (fun x => if f x = i then 1 else 0)

/-- `f ↦ f ∘ σ` preserves content. -/
def Words.comp {N ℓ : ℕ} {α : Fin ℓ → ℤ} (f : Words N ℓ α) (σ : Equiv.Perm (Fin N)) :
    Words N ℓ α :=
  ⟨f.1 ∘ σ, fun i => by
    have := card_filter_comp f.1 σ i
    simp only [Function.comp_apply]
    rw [this]; exact f.2 i⟩

/-- The permutation module `M^α` on functions on words of content `α`
(`(σ v) f = v (f ∘ σ)`, as for `OAI.Saxl.wordRep`). -/
def permRep (N ℓ : ℕ) (α : Fin ℓ → ℤ) :
    Representation ℂ (Equiv.Perm (Fin N)) (Words N ℓ α → ℂ) where
  toFun σ :=
    { toFun := fun v f => v (f.comp σ)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext v f; rfl
  map_mul' g h := by ext v f; rfl

end
end StrongConvW2HP.Q289
end

section
namespace StrongConvW2HP.Q289.PartB
open StrongConv OAI.Saxl StrongConvW2HP.Q289
open Finset
variable {N : ℕ} {Y : Type*} [DecidableEq Y]
lemma exists_word [Fintype Y] (c : Y → ℕ) (hc : ∑ y, c y = N) :
    ∃ h0 : Fin N → Y, ∀ y, (univ.filter fun x => h0 x = y).card = c y := by
  have e : Fin N ≃ Σ y, Fin (c y) := Fintype.equivOfCardEq (by simp [Fintype.card_sigma, hc])
  refine ⟨fun x => (e x).1, fun y => ?_⟩
  rw [Finset.card_equiv e (t := univ.filter fun s : (Σ y, Fin (c y)) => s.1 = y) (by simp)]
  rw [Finset.card_filter, Fintype.sum_sigma]
  simp [apply_ite Finset.card]

lemma exists_perm_of_cnt (h0 h : Fin N → Y)
    (hc : ∀ y, (univ.filter fun x => h x = y).card = (univ.filter fun x => h0 x = y).card) :
    ∃ τ : Equiv.Perm (Fin N), ∀ x, h0 (τ x) = h x := by
  have e : ∀ y, {a // h a = y} ≃ {b // h0 b = y} := fun y =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype, hc])
  exact ⟨Equiv.ofFiberEquiv e, fun x => Equiv.ofFiberEquiv_map e x⟩

lemma cnt_comp (h : Fin N → Y) (τ : Equiv.Perm (Fin N)) (y : Y) :
    (univ.filter fun x => h (τ x) = y).card = (univ.filter fun x => h x = y).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp τ (fun x => if h x = y then 1 else 0)

lemma sum_stab [Fintype Y] (c : Y → ℕ) (hc : ∑ y, c y = N) :
    ∑ h ∈ (univ.filter fun h : Fin N → Y => ∀ y, (univ.filter fun x => h x = y).card = c y),
      (univ.filter fun σ : Equiv.Perm (Fin N) => ∀ x, h (σ x) = h x).card = N.factorial := by
  obtain ⟨h0, hh0⟩ := exists_word c hc
  have hcard : (univ : Finset (Equiv.Perm (Fin N))).card = N.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← hcard, Finset.card_eq_sum_card_fiberwise (f := fun τ : Equiv.Perm (Fin N) => h0 ∘ τ)
    (t := univ.filter fun h : Fin N → Y => ∀ y, (univ.filter fun x => h x = y).card = c y)]
  · apply Finset.sum_congr rfl
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    obtain ⟨τ0, hτ0⟩ := exists_perm_of_cnt h0 h (fun y => by rw [hh, hh0])
    symm
    refine Finset.card_bij' (fun τ _ => τ0⁻¹ * τ) (fun σ _ => τ0 * σ) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      intro x
      calc h ((τ0⁻¹ * τ) x) = h0 (τ0 ((τ0⁻¹ * τ) x)) := (hτ0 _).symm
        _ = h0 (τ x) := by simp
        _ = h x := congrFun hτ x
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      funext x
      simp only [Function.comp_apply, Equiv.Perm.mul_apply, hτ0, hσ]
    · intro σ _; simp
    · intro τ _; simp
  · intro τ _
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    intro y
    rw [cnt_comp h0 τ y, hh0]

end StrongConvW2HP.Q289.PartB
end

section
namespace StrongConvW2HP.Q289.PartB
open StrongConv OAI.Saxl StrongConvW2HP.Q289
open Finset
lemma swap_count {A B : Type*} [Fintype A] [Fintype B] (P : A → B → Prop)
    [∀ a b, Decidable (P a b)] (R : B → Prop) [DecidablePred R] :
    ∑ a, (univ.filter fun b => P a b ∧ R b).card =
      ∑ b ∈ univ.filter R, (univ.filter fun a => P a b).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with hR <;> simp [hR]

lemma margin_fst {N ℓ : ℕ} (h : Fin N → Fin ℓ × Fin ℓ) (i : Fin ℓ) :
    ∑ j, (univ.filter fun x => h x = (i, j)).card = (univ.filter fun x => (h x).1 = i).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (h x).2) (t := univ) (by simp)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [Prod.ext_iff]

lemma margin_snd {N ℓ : ℕ} (h : Fin N → Fin ℓ × Fin ℓ) (j : Fin ℓ) :
    ∑ i, (univ.filter fun x => h x = (i, j)).card = (univ.filter fun x => (h x).2 = j).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (h x).1) (t := univ) (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [Prod.ext_iff, and_comm]

theorem burnside_tables {N ℓ : ℕ} (α β : Fin ℓ → ℤ) (hα : ∑ i, α i = N) (hβ : ∑ i, β i = N) :
    ∑ σ : Equiv.Perm (Fin N), xi α σ * xi β σ = N.factorial * tables N ℓ α β := by
  have step1 : ∀ σ : Equiv.Perm (Fin N), xi α σ * xi β σ =
      (univ.filter fun h : Fin N → Fin ℓ × Fin ℓ => (∀ x, h (σ x) = h x) ∧
        ((∀ i, ((univ.filter fun x => (h x).1 = i).card : ℤ) = α i) ∧
          ∀ j, ((univ.filter fun x => (h x).2 = j).card : ℤ) = β j)).card := by
    intro σ
    unfold xi
    rw [← Finset.card_product]
    refine Finset.card_nbij' (fun p x => (p.1 x, p.2 x))
      (fun h => (fun x => (h x).1, fun x => (h x).2)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and] at hp ⊢
      refine ⟨fun x => Prod.ext (hp.1.1 x) (hp.2.1 x), hp.1.2, hp.2.2⟩
    · intro h hh
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and] at hh ⊢
      refine ⟨⟨fun x => congrArg Prod.fst (hh.1 x), hh.2.1⟩,
        ⟨fun x => congrArg Prod.snd (hh.1 x), hh.2.2⟩⟩
    · intro p _; rfl
    · intro h _; rfl
  simp_rw [step1]
  -- swap the double count
  have step2 : ∑ σ : Equiv.Perm (Fin N),
      (univ.filter fun h : Fin N → Fin ℓ × Fin ℓ => (∀ x, h (σ x) = h x) ∧
        ((∀ i, ((univ.filter fun x => (h x).1 = i).card : ℤ) = α i) ∧
          ∀ j, ((univ.filter fun x => (h x).2 = j).card : ℤ) = β j)).card =
      ∑ h ∈ (univ.filter fun h : Fin N → Fin ℓ × Fin ℓ =>
        ((∀ i, ((univ.filter fun x => (h x).1 = i).card : ℤ) = α i) ∧
          ∀ j, ((univ.filter fun x => (h x).2 = j).card : ℤ) = β j)),
        (univ.filter fun σ : Equiv.Perm (Fin N) => ∀ x, h (σ x) = h x).card := by
    exact swap_count _ _
  rw [step2]
  have hle : ∀ (h : Fin N → Fin ℓ × Fin ℓ) (p : Fin ℓ × Fin ℓ),
      (univ.filter fun x => h x = p).card < N + 1 := fun h p =>
    Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))
  let g : (Fin N → Fin ℓ × Fin ℓ) → Fin ℓ → Fin ℓ → Fin (N + 1) :=
    fun h i j => ⟨(univ.filter fun x => h x = (i, j)).card, hle h (i, j)⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := g)
    (t := univ.filter fun M : Fin ℓ → Fin ℓ → Fin (N + 1) =>
      (∀ i, ((∑ j, (M i j : ℕ) : ℕ) : ℤ) = α i) ∧ ∀ j, ((∑ i, (M i j : ℕ) : ℕ) : ℤ) = β j)]
  · rw [Finset.sum_congr rfl (g := fun _ => N.factorial), Finset.sum_const, smul_eq_mul,
      mul_comm]
    · rfl
    intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    have hset : ((univ.filter fun h : Fin N → Fin ℓ × Fin ℓ =>
        ((∀ i, ((univ.filter fun x => (h x).1 = i).card : ℤ) = α i) ∧
          ∀ j, ((univ.filter fun x => (h x).2 = j).card : ℤ) = β j)).filter
            fun h => g h = M) =
        univ.filter fun h : Fin N → Fin ℓ × Fin ℓ =>
          ∀ p, (univ.filter fun x => h x = p).card = (M p.1 p.2 : ℕ) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hg⟩ p
        have := congrFun (congrFun hg p.1) p.2
        exact congrArg Fin.val this
      · intro hc
        refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_⟩
        · rw [← margin_fst, Finset.sum_congr rfl (fun j _ => hc (i, j))]
          exact hM.1 i
        · rw [← margin_snd, Finset.sum_congr rfl (fun i _ => hc (i, j))]
          exact hM.2 j
        · funext i j
          exact Fin.ext (hc (i, j))
    rw [hset]
    apply sum_stab
    rw [Fintype.sum_prod_type]
    have : ((∑ i, ∑ j, (M i j : ℕ) : ℕ) : ℤ) = N := by
      rw [← hα, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun i _ => hM.1 i)
    exact_mod_cast this
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    refine ⟨fun i => ?_, fun j => ?_⟩
    · rw [← hh.1 i, ← margin_fst]
    · rw [← hh.2 j, ← margin_snd]

end StrongConvW2HP.Q289.PartB
end

section
open StrongConv OAI.Saxl
namespace StrongConvW2HP.Q289
noncomputable section
/-! ## Stubs -/
alias burnside_tables := StrongConvW2HP.Q289.PartB.burnside_tables

end
end StrongConvW2HP.Q289
end

section
open StrongConv OAI.Saxl StrongConvW2HP.Q289
namespace StrongConvW2HP.Q289.PartC
open Finset
noncomputable section
/-!
# q289 Part C: the alternant identity for tables

Route (Macdonald I.3): in `ℤ[y_0, …, y_{n-1}]`, `h_m` is the coefficient of `t^m` in
`∏_j 1/(1 - y_j t)`; `#tables(α, β) = coeff_β ∏_i h_{α_i}`; the Jacobi–Trudi/bialternant
identity `det[y_j^{a_i}] = det[y_j^{δ_i}] · det[h_{a_i - δ_j}]` follows from the matrix
factorisation `(y_j^{a_i}) = (h_{a_i - δ_k}) · (coeff_{δ_k} ∏_{i ≠ j} (1 - y_i t))`
(applied to `a` and to `δ`, where the `h`-matrix is unitriangular).
-/
/-- The polynomial ring. -/
abbrev Rg (n : ℕ) := MvPolynomial (Fin n) ℤ

/-- The geometric series `1/(1 - y_j t)`. -/
def G {n : ℕ} (j : Fin n) : PowerSeries (Rg n) := PowerSeries.mk fun m => MvPolynomial.X j ^ m

/-- `∏_j 1/(1 - y_j t)`. -/
def Gall (n : ℕ) : PowerSeries (Rg n) := ∏ j, G j

/-- The complete homogeneous symmetric polynomial `h_m`. -/
def h (n m : ℕ) : Rg n := PowerSeries.coeff m (Gall n)

/-- `h` at an integer index (zero for negative indices). -/
def hz (n : ℕ) (z : ℤ) : Rg n := if z < 0 then 0 else h n z.toNat

/-- `∏_{i ≠ j} (1 - y_i t)`. -/
def Q {n : ℕ} (j : Fin n) : PowerSeries (Rg n) :=
  ∏ i ∈ univ.erase j, (1 - PowerSeries.C (MvPolynomial.X i) * PowerSeries.X)

lemma one_sub_mul_G {n : ℕ} (i : Fin n) :
    (1 - PowerSeries.C (MvPolynomial.X i) * PowerSeries.X) * G i = 1 := by
  refine PowerSeries.ext fun m => ?_
  rcases m with _ | m
  · simp [G, sub_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul]
    simp [G, PowerSeries.coeff_mk, pow_succ, PowerSeries.coeff_one]
    ring

lemma Q_mul_Gall {n : ℕ} (j : Fin n) : Q j * Gall n = G j := by
  unfold Gall Q
  rw [← Finset.mul_prod_erase univ G (mem_univ j), mul_left_comm, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one (fun i _ => one_sub_mul_G i), mul_one]

lemma coeff_prod_one_sub {n : ℕ} (s : Finset (Fin n)) : ∀ p, s.card < p →
    PowerSeries.coeff p
      (∏ i ∈ s, (1 - PowerSeries.C (MvPolynomial.X i) * PowerSeries.X : PowerSeries (Rg n))) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro p hp
    simp only [prod_empty, PowerSeries.coeff_one]
    simp at hp
    rw [if_neg (by omega)]
  | insert a s ha ih =>
    intro p hp
    rw [Finset.card_insert_of_notMem ha] at hp
    obtain ⟨p, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Finset.prod_insert ha, sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, ih _ (by omega), ih _ (by omega)]
    simp

lemma h_zero (n : ℕ) : h n 0 = 1 := by
  rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply, Gall, map_prod]
  exact Finset.prod_eq_one (fun j _ => by simp [G])

/-- The key identity `∑_k h_{m - δ_k} c_{δ_k} = y_j^m`. -/
lemma key {n : ℕ} (j : Fin n) (m : ℕ) :
    ∑ k : Fin n, hz n ((m : ℤ) - (Fin.rev k : ℕ)) * PowerSeries.coeff (Fin.rev k : ℕ) (Q j) =
      MvPolynomial.X j ^ m := by
  set f : ℕ → Rg n := fun p => hz n ((m : ℤ) - p) * PowerSeries.coeff p (Q j) with hf
  have h1 : ∑ k : Fin n, hz n ((m : ℤ) - (Fin.rev k : ℕ)) * PowerSeries.coeff (Fin.rev k : ℕ) (Q j)
      = ∑ p ∈ range n, f p := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Equiv.sum_comp Fin.revPerm (fun k : Fin n => f k)
  have h2 : ∑ p ∈ range n, f p = ∑ p ∈ range (m + n + 1), f p := by
    apply Finset.sum_subset (by intro p; simp; omega)
    intro p hp hpn
    simp at hp hpn
    simp only [hf]
    have := j.pos
    rw [Q, coeff_prod_one_sub _ p (by rw [Finset.card_erase_of_mem (mem_univ _)]; simp; omega),
      mul_zero]
  have h3 : ∑ p ∈ range (m + 1), f p = ∑ p ∈ range (m + n + 1), f p := by
    apply Finset.sum_subset (by intro p; simp; omega)
    intro p hp hpn
    simp at hp hpn
    simp only [hf, hz]
    rw [if_pos (by omega), zero_mul]
  have h4 : MvPolynomial.X j ^ m = ∑ p ∈ range (m + 1), f p := by
    have : MvPolynomial.X j ^ m = PowerSeries.coeff m (Q j * Gall n) := by
      rw [Q_mul_Gall, G, PowerSeries.coeff_mk]
    rw [this, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun p q => PowerSeries.coeff p (Q j) * PowerSeries.coeff q (Gall n))]
    apply Finset.sum_congr rfl
    intro p hp
    simp at hp
    simp only [hf, hz]
    rw [if_neg (by omega), mul_comm]
    have : ((m : ℤ) - p).toNat = m - p := by omega
    rw [this, h]
  rw [h1, h2, ← h3, h4]

/-- `Y_e = (y_j^{e_i})`. -/
def Y {n : ℕ} (e : Fin n → ℕ) : Matrix (Fin n) (Fin n) (Rg n) := fun i j => MvPolynomial.X j ^ e i

/-- `H_e = (h_{e_i - δ_k})`. -/
def H {n : ℕ} (e : Fin n → ℕ) : Matrix (Fin n) (Fin n) (Rg n) :=
  fun i k => hz n ((e i : ℤ) - (Fin.rev k : ℕ))

/-- `E = (coeff_{δ_k} Q_j)`. -/
def E (n : ℕ) : Matrix (Fin n) (Fin n) (Rg n) := fun k j => PowerSeries.coeff (Fin.rev k : ℕ) (Q j)

lemma H_mul_E {n : ℕ} (e : Fin n → ℕ) : H e * E n = Y e := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_apply, H, E, Y]
  exact key j (e i)

/-- `δ`. -/
def dl (n : ℕ) : Fin n → ℕ := fun i => (Fin.rev i : ℕ)

lemma det_H_dl (n : ℕ) : (H (dl n)).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one (fun i _ => ?_)
    simp [H, dl, hz, h_zero]
  · intro i k hki
    simp only [id] at hki
    have := Fin.lt_def.mp hki
    simp [H, dl, hz]
    exact fun h' => absurd h' (not_le.mpr hki)

lemma bialternant {n : ℕ} (e : Fin n → ℕ) : (Y e).det = (Y (dl n)).det * (H e).det := by
  rw [← H_mul_E, ← H_mul_E, Matrix.det_mul, Matrix.det_mul, det_H_dl, one_mul, mul_comm]

/-! ## Monomials and coefficient extraction -/
/-- An exponent vector as a finsupp. -/
abbrev eqs {n : ℕ} (e : Fin n → ℕ) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm e

/-- The monomial `y^d`. -/
def mono {n : ℕ} (d : Fin n → ℕ) : Rg n := ∏ j, MvPolynomial.X j ^ d j

lemma mono_eq {n : ℕ} (d : Fin n → ℕ) : mono d = MvPolynomial.monomial (eqs d) 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [mono]

lemma coeff_mono {n : ℕ} (a d : Fin n → ℕ) :
    MvPolynomial.coeff (eqs a) (mono d) = if d = a then 1 else 0 := by
  rw [mono_eq, MvPolynomial.coeff_monomial]
  simp only [EmbeddingLike.apply_eq_iff_eq]

/-- The coefficient at an integer exponent vector (zero if some entry is negative). -/
def cf {n : ℕ} (β : Fin n → ℤ) (P : Rg n) : ℤ :=
  if ∀ j, 0 ≤ β j then MvPolynomial.coeff (eqs fun j => (β j).toNat) P else 0

lemma coeff_mono_mul {n : ℕ} (a d : Fin n → ℕ) (P : Rg n) :
    MvPolynomial.coeff (eqs a) (mono d * P) = cf (fun j => (a j : ℤ) - d j) P := by
  rw [mono_eq, MvPolynomial.coeff_monomial_mul']
  unfold cf
  by_cases hda : ∀ j, d j ≤ a j
  · rw [if_pos, if_pos, one_mul]
    · congr 1; ext j; simp
    · intro j; have := hda j; beta_reduce; omega
    · rw [Finsupp.le_def]; intro j; simpa using hda j
  · rw [if_neg, if_neg]
    · push Not at hda ⊢; obtain ⟨j, hj⟩ := hda; exact ⟨j, by omega⟩
    · rw [Finsupp.le_def]; push Not at hda ⊢; obtain ⟨j, hj⟩ := hda; exact ⟨j, by simpa using hj⟩

lemma det_Y {n : ℕ} (e : Fin n → ℕ) :
    (Y e).det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • mono (e ∘ σ) := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def]
  rfl

lemma det_H {n : ℕ} (e : Fin n → ℕ) :
    (H e).det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • ∏ i, H e i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def]
  rfl

lemma coeff_det_Y {n : ℕ} (a : Fin n → ℕ) (ha : Function.Injective a) :
    MvPolynomial.coeff (eqs a) (Y a).det = 1 := by
  rw [det_Y, MvPolynomial.coeff_sum, Finset.sum_eq_single 1]
  · simp [coeff_mono]
  · intro σ _ hσ
    rw [MvPolynomial.coeff_smul, coeff_mono, if_neg, smul_zero]
    intro h'
    exact hσ (Equiv.ext fun i => ha (congrFun h' i))
  · simp

/-! ## Tables as coefficients -/
lemma h_eq (n m : ℕ) :
    h n m = ∑ l ∈ (univ : Finset (Fin n)).finsuppAntidiag m, ∏ j, MvPolynomial.X j ^ l j := by
  rw [h, Gall, PowerSeries.coeff_prod]
  simp [G, PowerSeries.coeff_mk]

lemma prod_h (n : ℕ) (r : Fin n → ℕ) :
    ∏ i, h n (r i) =
      ∑ L ∈ Fintype.piFinset (fun i => (univ : Finset (Fin n)).finsuppAntidiag (r i)),
        mono (fun j => ∑ i, L i j) := by
  simp only [h_eq]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  simp only [mono]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]

lemma coeff_prod_h (n : ℕ) (r e : Fin n → ℕ) :
    MvPolynomial.coeff (eqs e) (∏ i, h n (r i)) =
      (((Fintype.piFinset fun i => (univ : Finset (Fin n)).finsuppAntidiag (r i)).filter
        fun L => (fun j => ∑ i, L i j) = e).card : ℤ) := by
  rw [prod_h, MvPolynomial.coeff_sum]
  simp only [coeff_mono]
  rw [Finset.sum_boole]

lemma tables_nat (N n : ℕ) (r e : Fin n → ℕ) (hr : ∑ i, r i = N) :
    tables N n (fun i => (r i : ℤ)) (fun j => (e j : ℤ)) =
      ((Fintype.piFinset fun i => (univ : Finset (Fin n)).finsuppAntidiag (r i)).filter
        fun L => (fun j => ∑ i, L i j) = e).card := by
  unfold tables
  simp only [Nat.cast_inj]
  apply Finset.card_bij (fun M _ => fun i => eqs (fun j => (M i j : ℕ)))
  · intro M hM
    simp only [mem_filter, mem_univ, true_and] at hM
    simp only [mem_filter, Fintype.mem_piFinset, mem_finsuppAntidiag]
    refine ⟨fun i => ⟨by simpa using hM.1 i, by simp⟩, ?_⟩
    funext j; simpa using hM.2 j
  · intro M₁ _ M₂ _ heq
    funext i j
    have := congrArg (fun L => L i j) heq
    simp at this
    exact Fin.ext this
  · intro L hL
    simp only [mem_filter, Fintype.mem_piFinset, mem_finsuppAntidiag] at hL
    have hle : ∀ i j, L i j ≤ N := by
      intro i j
      calc L i j ≤ ∑ k, L i k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
        _ = r i := (hL.1 i).1
        _ ≤ N := hr ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    refine ⟨fun i j => ⟨L i j, Nat.lt_succ_of_le (hle i j)⟩, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      refine ⟨fun i => ?_, fun j => ?_⟩
      · simpa using (hL.1 i).1
      · simpa using congrFun hL.2 j
    · funext i; ext j; simp

lemma tables_eq (N n : ℕ) (α β : Fin n → ℤ) (hα : ∑ i, α i = N) :
    (tables N n α β : ℤ) = cf β (∏ i, hz n (α i)) := by
  by_cases hneg : ∃ i, α i < 0
  · obtain ⟨i, hi⟩ := hneg
    have h0 : tables N n α β = 0 := by
      unfold tables
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro M - ⟨h1, -⟩
      have := h1 i
      omega
    rw [h0, Finset.prod_eq_zero (mem_univ i) (by simp [hz, hi])]
    simp [cf]
  push Not at hneg
  by_cases hβ : ∀ j, 0 ≤ β j
  · have hα' : α = fun i => ((α i).toNat : ℤ) := by funext i; have := hneg i; omega
    have hβ' : β = fun j => ((β j).toNat : ℤ) := by funext j; have := hβ j; omega
    have hr : ∑ i, (α i).toNat = N := by
      have : ((∑ i, (α i).toNat : ℕ) : ℤ) = N := by
        push_cast; rw [← hα]; exact Finset.sum_congr rfl fun i _ => by have := hneg i; omega
      exact_mod_cast this
    unfold cf
    rw [if_pos hβ]
    have hP : ∏ i, hz n (α i) = ∏ i, h n (α i).toNat :=
      Finset.prod_congr rfl fun i _ => by simp [hz, not_lt.mpr (hneg i)]
    have ht := tables_nat N n (fun i => (α i).toNat) (fun j => (β j).toNat) hr
    rw [hP, coeff_prod_h]
    conv_lhs => rw [hα', hβ']
    rw [ht]
  · push Not at hβ
    obtain ⟨j, hj⟩ := hβ
    have h0 : tables N n α β = 0 := by
      unfold tables
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro M - ⟨-, h2⟩
      have := h2 j
      omega
    unfold cf
    rw [h0, if_neg (by push Not; exact ⟨j, hj⟩)]
    simp

/-! ## The main theorem -/
theorem alternant_tables (N : ℕ) (rows : List ℕ) (hsorted : rows.SortedGE)
    (hsum : rows.sum = N) :
    ∑ w : Equiv.Perm (Fin rows.length), ∑ w' : Equiv.Perm (Fin rows.length),
      (Equiv.Perm.sign w : ℤ) * (Equiv.Perm.sign w' : ℤ) *
        (tables N rows.length (alphaW rows w) (alphaW rows w') : ℤ) = 1 := by
  set a : Fin rows.length → ℕ := fun i => rows.get i + (Fin.rev i : ℕ) with ha_def
  have ha : Function.Injective a := by
    apply StrictAnti.injective
    intro i j hij
    have h1 := hsorted.antitone_get hij.le
    have h2 := Fin.lt_def.mp hij
    have := i.isLt
    have := j.isLt
    simp only [ha_def, Fin.val_rev]
    omega
  have hα : ∀ w : Equiv.Perm (Fin rows.length),
      alphaW rows w = fun i => (a i : ℤ) - (dl rows.length (w i) : ℕ) := by
    intro w; funext i
    simp only [alphaW, ha_def, dl, Fin.val_rev]
    have := i.isLt; have := (w i).isLt
    omega
  have hsumα : ∀ w : Equiv.Perm (Fin rows.length), ∑ i, alphaW rows w i = N := by
    intro w
    simp only [alphaW, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp w (fun i => ((i : ℕ) : ℤ))]
    have : ∑ i : Fin rows.length, (rows.get i : ℤ) = ((∑ i : Fin rows.length, rows.get i : ℕ) : ℤ) := by
      push_cast; rfl
    rw [this]
    simp [hsum]
  have hterm : ∀ w w' : Equiv.Perm (Fin rows.length),
      (tables N rows.length (alphaW rows w) (alphaW rows w') : ℤ) =
        MvPolynomial.coeff (eqs a) (mono (dl rows.length ∘ w') * ∏ i, H a i (w i)) := by
    intro w w'
    rw [tables_eq N _ _ _ (hsumα w), coeff_mono_mul, hα w, hα w']
    rfl
  have hdet : MvPolynomial.coeff (eqs a) ((Y (dl rows.length)).det * (H a).det) = 1 := by
    rw [← bialternant]; exact coeff_det_Y a ha
  rw [← hdet, det_Y, det_H, Finset.sum_mul_sum]
  simp only [MvPolynomial.coeff_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  rw [hterm, smul_mul_smul_comm, MvPolynomial.coeff_smul, smul_eq_mul]
  ring

end
end StrongConvW2HP.Q289.PartC
end

section
open StrongConv OAI.Saxl
namespace StrongConvW2HP.Q289
noncomputable section
alias alternant_tables := StrongConvW2HP.Q289.PartC.alternant_tables

end
end StrongConvW2HP.Q289
end

section
namespace StrongConvW2HP.Q289.PartR
open StrongConv OAI.Saxl StrongConvW2HP.Q289
noncomputable section
/-! ## `permRep_char` -/
theorem permRep_char {N ℓ : ℕ} (α : Fin ℓ → ℤ) (σ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (Words N ℓ α → ℂ) (permRep N ℓ α σ) = (xi α σ : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Words N ℓ α)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  have h1 : ∀ f : Words N ℓ α, (permRep N ℓ α σ) (Pi.single f 1) f =
      if f.comp σ = f then 1 else 0 := by
    intro f
    change (Pi.single f (1 : ℂ) : Words N ℓ α → ℂ) (f.comp σ) = _
    simp [Pi.single_apply]
  simp only [h1]
  rw [Finset.sum_boole]
  congr 1
  unfold xi
  apply Finset.card_bij (fun f _ => f.1)
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    refine ⟨fun x => ?_, f.2⟩
    have := congrArg (fun g : Words N ℓ α => g.1 x) hf
    exact this
  · intro f _ g _ h
    exact Subtype.ext h
  · intro f hf
    replace hf := (Finset.mem_filter.mp hf).2
    refine ⟨⟨f, hf.2⟩, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    funext x
    exact hf.1 x

/-! ## `specht_char_inv` -/
theorem specht_char_inv {N : ℕ} {μ : YoungDiagram} (t : Tableau N μ) (σ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (Specht t) (spechtRep t σ⁻¹) =
      LinearMap.trace ℂ (Specht t) (spechtRep t σ) := by
  have hc : IsConj σ σ⁻¹ :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (Equiv.Perm.cycleType_inv σ).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have := Representation.char_conj (spechtRep t) σ c
  rw [hc] at this
  exact this

/-! ## `young_specht` -/
theorem tabRow_cons' (r : ℕ) (rows : List ℕ) (x : ℕ) :
    tabRow (r :: rows) x = if r ≤ x then tabRow rows (x - r) + 1 else 0 := by
  unfold tabRow
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  have h0 : (List.take (0 + 1) (r :: rows)).sum = r := by simp
  by_cases h : r ≤ x
  · have hp : ((fun i => decide ((List.take (i + 1) (r :: rows)).sum ≤ x)) ∘ Nat.succ) =
        fun i => decide ((rows.take (i+1)).sum ≤ x - r) := by
      funext i
      show decide ((List.take (i + 1 + 1) (r :: rows)).sum ≤ x) = _
      rw [List.take_succ_cons, List.sum_cons]
      simp only [decide_eq_decide]
      omega
    rw [hp, h0, if_pos (by simpa using h), if_pos h, List.length_cons, List.length_map]
  · have hp : ((fun i => decide ((List.take (i + 1) (r :: rows)).sum ≤ x)) ∘ Nat.succ) =
        fun _ => false := by
      funext i
      show decide ((List.take (i + 1 + 1) (r :: rows)).sum ≤ x) = _
      rw [List.take_succ_cons, List.sum_cons]
      simp only [decide_eq_false_iff_not]
      omega
    rw [hp, h0, if_neg (by simpa using h), if_neg h, List.length_map]
    simp

theorem tabCol_cons' (r : ℕ) (rows : List ℕ) (x : ℕ) :
    tabCol (r :: rows) x = if r ≤ x then tabCol rows (x - r) else x := by
  unfold tabCol
  rw [tabRow_cons']
  split_ifs with h
  · simp only [List.take_succ_cons, List.sum_cons]
    omega
  · simp

lemma tab_append_zeros (L : List ℕ) (k x : ℕ) (hx : x < L.sum) :
    tabRow (L ++ List.replicate k 0) x = tabRow L x ∧
      tabCol (L ++ List.replicate k 0) x = tabCol L x := by
  induction L generalizing x with
  | nil => simp at hx
  | cons r L ih =>
    rw [List.cons_append, tabRow_cons', tabRow_cons', tabCol_cons', tabCol_cons']
    split_ifs with h
    · have := ih (x - r) (by simp only [List.sum_cons] at hx; omega)
      exact ⟨by rw [this.1], this.2⟩
    · exact ⟨rfl, rfl⟩

lemma youngSymmetrizer_append_zeros (N : ℕ) (L : List ℕ) (k : ℕ) (hL : L.sum = N) :
    youngSymmetrizer N (L ++ List.replicate k 0) = youngSymmetrizer N L := by
  have hr : ∀ x : Fin N, tabRow (L ++ List.replicate k 0) (x : ℕ) = tabRow L x :=
    fun x => (tab_append_zeros L k x (hL ▸ x.2)).1
  have hc : ∀ x : Fin N, tabCol (L ++ List.replicate k 0) (x : ℕ) = tabCol L x :=
    fun x => (tab_append_zeros L k x (hL ▸ x.2)).2
  unfold youngSymmetrizer
  simp only [hr, hc]

lemma sorted_split (rows : List ℕ) (h : rows.Pairwise (· ≥ ·)) :
    ∃ (L : List ℕ) (k : ℕ), rows = L ++ List.replicate k 0 ∧ ∀ x ∈ L, 0 < x := by
  induction rows with
  | nil => exact ⟨[], 0, rfl, by simp⟩
  | cons a rest ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨L, k, rfl, hL⟩ := ih h.2
    by_cases ha : a = 0
    · subst ha
      cases L with
      | nil => exact ⟨[], k + 1, by simp [List.replicate_succ], by simp⟩
      | cons b L =>
        exfalso
        have h1 := h.1 b (by simp)
        have h2 := hL b (by simp)
        omega
    · refine ⟨a :: L, k, rfl, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact hL x hx

lemma trace_youngAct_congr {N : ℕ} {L L' : List ℕ}
    (h : youngSymmetrizer N L = youngSymmetrizer N L') (σ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (youngSpace N L) (youngAct N L σ) =
      LinearMap.trace ℂ (youngSpace N L') (youngAct N L' σ) := by
  obtain ⟨e⟩ := HananyPuder.W2HP.PartB.youngEquivOfEq h
  exact congrFun (Representation.char_iso e) σ

theorem young_specht (N : ℕ) (rows : List ℕ) (hsorted : rows.SortedGE) (hsum : rows.sum = N) :
    ∃ (μ : YoungDiagram) (t : Tableau N μ),
      (∀ σ, LinearMap.trace ℂ (youngSpace N rows) (youngAct N rows σ) =
        LinearMap.trace ℂ (Specht t) (spechtRep t σ)) ∧
      (∀ i : Fin rows.length, rows.get i = μ.rowLen i) ∧ μ.colLen 0 ≤ rows.length := by
  obtain ⟨L, k, hrows, hpos⟩ := sorted_split rows hsorted.pairwise
  have hLs : L.SortedGE := by
    have := hsorted.pairwise
    rw [hrows, List.pairwise_append] at this
    exact this.1.sortedGE
  subst hrows
  have hrl : (YoungDiagram.ofRowLens L hLs).rowLens = L :=
    YoungDiagram.rowLens_ofRowLens_eq_self hpos
  have hLsum : L.sum = N := by rw [← hsum]; simp
  have hcard : (YoungDiagram.ofRowLens L hLs).card = N := by
    rw [card_eq_sum_rowLens, hrl, hLsum]
  let t := canonicalTableau (YoungDiagram.ofRowLens L hLs) hcard
  obtain ⟨e, he⟩ := exists_linearEquiv_youngSpace_specht t
  refine ⟨YoungDiagram.ofRowLens L hLs, t, fun σ => ?_, fun i => ?_, ?_⟩
  · rw [trace_youngAct_congr (L' := (YoungDiagram.ofRowLens L hLs).rowLens)
      (by rw [hrl, youngSymmetrizer_append_zeros N L k hLsum]) σ]
    let E : Representation.Equiv (HananyPuder.W2HP.PartB.youngRep N
        (YoungDiagram.ofRowLens L hLs).rowLens) (spechtRep t) :=
      Representation.Equiv.mk e (fun g => LinearMap.ext fun x => he g x)
    exact congrFun (Representation.char_iso E) σ
  · rw [List.get_eq_getElem]
    by_cases hi : (i : ℕ) < L.length
    · rw [List.getElem_append_left hi]
      exact (YoungDiagram.rowLen_ofRowLens (hw := hLs) ⟨i, hi⟩).symm
    · rw [List.getElem_append_right (by omega), List.getElem_replicate]
      by_contra hne
      have hm : ((i : ℕ), 0) ∈ YoungDiagram.ofRowLens L hLs :=
        YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      obtain ⟨h1, _⟩ := YoungDiagram.mem_ofRowLens.mp hm
      exact hi h1
  · rw [← YoungDiagram.length_rowLens, hrl]
    simp

end
end StrongConvW2HP.Q289.PartR
end

section
open StrongConv OAI.Saxl
namespace StrongConvW2HP.Q289
noncomputable section
alias young_specht := StrongConvW2HP.Q289.PartR.young_specht

alias specht_char_inv := StrongConvW2HP.Q289.PartR.specht_char_inv

alias permRep_char := StrongConvW2HP.Q289.PartR.permRep_char

end
end StrongConvW2HP.Q289
end

section
namespace StrongConvW2HP.Q289.PartR
open StrongConv OAI.Saxl StrongConvW2HP.Q289
noncomputable section
/-! ## `hom_incl` -/
/-- Words over `Fin ℓ` with all letters `< c` read as words over `Fin c`. -/
def phi (N ℓ c : ℕ) (α : Fin ℓ → ℤ) : WordSpace N c →ₗ[ℂ] (Words N ℓ α → ℂ) where
  toFun v f := if h : ∀ x, ((f.1 x : Fin ℓ) : ℕ) < c then v (fun x => ⟨f.1 x, h x⟩) else 0
  map_add' v w := by
    funext f
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' a v := by
    funext f
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

lemma phi_comm {N ℓ c : ℕ} (α : Fin ℓ → ℤ) (σ : Equiv.Perm (Fin N)) (v : WordSpace N c) :
    phi N ℓ c α (wordRep N c σ v) = permRep N ℓ α σ (phi N ℓ c α v) := by
  funext f
  change (if h : ∀ x, ((f.1 x : Fin ℓ) : ℕ) < c then
      wordRep N c σ v (fun x => ⟨f.1 x, h x⟩) else 0) =
    (if h : ∀ x, (((f.comp σ).1 x : Fin ℓ) : ℕ) < c then
      v (fun x => ⟨(f.comp σ).1 x, h x⟩) else 0)
  have hiff : (∀ x, ((f.1 x : Fin ℓ) : ℕ) < c) ↔ ∀ x, (((f.comp σ).1 x : Fin ℓ) : ℕ) < c := by
    constructor
    · intro h x; exact h (σ x)
    · intro h x
      have := h (σ⁻¹ x)
      change ((f.1 (σ (σ⁻¹ x)) : Fin ℓ) : ℕ) < c at this
      simpa using this
  by_cases h : ∀ x, ((f.1 x : Fin ℓ) : ℕ) < c
  · rw [dif_pos h, dif_pos (hiff.mp h)]; rfl
  · rw [dif_neg h, dif_neg (fun h' => h (hiff.mpr h'))]

/-- The inclusion `S^μ → M^α`. -/
def theta {N ℓ : ℕ} {μ : YoungDiagram} (t : Tableau N μ) (α : Fin ℓ → ℤ) :
    Representation.IntertwiningMap (spechtRep t) (permRep N ℓ α) where
  toLinearMap := (phi N ℓ (μ.colLen 0) α).comp (Specht t).subtype
  isIntertwining' g := LinearMap.ext fun x => phi_comm α g x.1

theorem hom_incl {N ℓ : ℕ} {μ : YoungDiagram} (t : Tableau N μ) (α : Fin ℓ → ℤ)
    (hα : ∀ i : Fin ℓ, α i = μ.rowLen i) (hℓ : μ.colLen 0 ≤ ℓ) :
    1 ≤ Module.finrank ℂ (Representation.IntertwiningMap (spechtRep t) (permRep N ℓ α)) := by
  classical
  let f0 : Words N ℓ α := ⟨fun x => Fin.castLE hℓ (rowWord t x), fun i => by
    rw [hα, HananyPuder.W2HP.PartR.rowLen_eq_count t i]
    congr 2
    apply Finset.filter_congr
    intro x _
    rw [Fin.ext_iff]
    rfl⟩
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  have hv : theta t α p f0 = 1 := by
    change (if h : ∀ x, ((f0.1 x : Fin ℓ) : ℕ) < μ.colLen 0 then
      polytabloid t (fun x => ⟨f0.1 x, h x⟩) else 0) = 1
    have hc : ∀ x, ((f0.1 x : Fin ℓ) : ℕ) < μ.colLen 0 := fun x => (rowWord t x).2
    rw [dif_pos hc]
    have : (fun x => (⟨f0.1 x, hc x⟩ : Fin (μ.colLen 0))) = rowWord t := by
      funext x; rfl
    rw [this]
    exact HananyPuder.W2HP.PartR.polytabloid_rowWord t
  apply Nat.one_le_iff_ne_zero.mpr
  apply Nat.pos_iff_ne_zero.mp
  apply (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mpr
  refine ⟨theta t α, fun h0 => ?_⟩
  rw [h0] at hv
  exact zero_ne_one hv

/-! ## `hom_dominance` -/
lemma col_count_le {N ℓ : ℕ} {μ : YoungDiagram} (t : Tableau N μ) (u : Fin N → Fin ℓ)
    (hu : ∀ i j, (t i).val.2 = (t j).val.2 → u i = u j → i = j) (k c : ℕ) :
    (Finset.univ.filter fun x => (u x : ℕ) < k ∧ (t x).val.2 = c).card ≤
      (Finset.univ.filter fun x => (t x).val.1 < k ∧ (t x).val.2 = c).card := by
  classical
  set A := Finset.univ.filter fun x => (u x : ℕ) < k ∧ (t x).val.2 = c with hA
  set B := Finset.univ.filter fun x => (t x).val.1 < k ∧ (t x).val.2 = c with hB
  set C := Finset.univ.filter fun x : Fin N => (t x).val.2 = c with hC
  have hAk : A.card ≤ k := by
    have := Finset.card_le_card_of_injOn (fun x => (u x : ℕ)) (s := A) (t := Finset.range k)
      (fun x hx => by
        have hx' := (Finset.mem_filter.mp hx).2
        exact Finset.mem_range.mpr hx'.1)
      (fun x hx y hy hxy => by
        have hx' := (Finset.mem_filter.mp hx).2
        have hy' := (Finset.mem_filter.mp hy).2
        exact hu x y (hx'.2.trans hy'.2.symm) (Fin.ext hxy))
    simpa using this
  by_cases hBC : C ⊆ B
  · calc A.card ≤ C.card := Finset.card_le_card (fun x hx => by
          have hx' := (Finset.mem_filter.mp hx).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'.2⟩)
      _ ≤ B.card := Finset.card_le_card hBC
  · obtain ⟨x, hxC, hxB⟩ := Finset.not_subset.mp hBC
    have hxc : (t x).val.2 = c := (Finset.mem_filter.mp hxC).2
    have hxk : k ≤ (t x).val.1 := by
      by_contra hlt
      exact hxB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, hxc⟩)
    have hx' : ((t x).val.1, (t x).val.2) ∈ μ := (t x).property
    rw [hxc] at hx'
    have hmem : ∀ r < k, (r, c) ∈ μ := fun r hr => μ.up_left_mem (by omega) le_rfl hx'
    calc A.card ≤ k := hAk
      _ = (Finset.range k).card := (Finset.card_range k).symm
      _ ≤ B.card := by
        apply Finset.card_le_card_of_injOn
          (fun r => if h : r < k then t.symm ⟨(r, c), hmem r h⟩ else x)
        · intro r hr
          have hr' : r < k := Finset.mem_range.mp hr
          simp only [dif_pos hr']
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hr', by simp⟩
        · intro r hr r' hr' he
          have h1 : r < k := Finset.mem_range.mp hr
          have h2 : r' < k := Finset.mem_range.mp hr'
          simp only [dif_pos h1, dif_pos h2] at he
          have := congrArg (fun y : μ.cells => (y : ℕ × ℕ).1) (t.symm.injective he)
          exact this

lemma total_le {N ℓ : ℕ} {μ : YoungDiagram} (t : Tableau N μ) (u : Fin N → Fin ℓ)
    (hu : ∀ i j, (t i).val.2 = (t j).val.2 → u i = u j → i = j) (k : ℕ) :
    (Finset.univ.filter fun x => (u x : ℕ) < k).card ≤ ∑ i ∈ Finset.range k, μ.rowLen i := by
  classical
  have hS : (Finset.univ.filter fun x => (u x : ℕ) < k).card =
      ∑ c ∈ Finset.univ.image (fun x => (t x).val.2),
        (Finset.univ.filter fun x => (u x : ℕ) < k ∧ (t x).val.2 = c).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (t x).val.2)
      (t := Finset.univ.image (fun x => (t x).val.2))
      (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.filter_filter]
  have hR0 : ∑ i ∈ Finset.range k, μ.rowLen i =
      (Finset.univ.filter fun x => (t x).val.1 < k).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (t x).val.1) (t := Finset.range k)
      (fun x hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2)]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    rw [HananyPuder.W2HP.PartR.rowLen_eq_count t i, Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro rfl; exact ⟨hi', rfl⟩
    · exact fun h => h.2
  have hR : ∑ i ∈ Finset.range k, μ.rowLen i =
      ∑ c ∈ Finset.univ.image (fun x => (t x).val.2),
        (Finset.univ.filter fun x => (t x).val.1 < k ∧ (t x).val.2 = c).card := by
    rw [hR0, Finset.card_eq_sum_card_fiberwise (f := fun x => (t x).val.2)
      (t := Finset.univ.image (fun x => (t x).val.2))
      (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.filter_filter]
  rw [hS, hR]
  exact Finset.sum_le_sum fun c _ => col_count_le t u hu k c

lemma sum_alpha_eq {N ℓ : ℕ} (α : Fin ℓ → ℤ) (u : Words N ℓ α) (k : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin ℓ => (i : ℕ) < k), α i =
      ((Finset.univ.filter fun x => ((u.1 x : Fin ℓ) : ℕ) < k).card : ℤ) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := u.1)
    (t := Finset.univ.filter (fun i : Fin ℓ => (i : ℕ) < k))
    (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : (i : ℕ) < k := (Finset.mem_filter.mp hi).2
  rw [← u.2 i, Finset.filter_filter]
  congr 2
  apply Finset.filter_congr
  intro x _
  constructor
  · intro h; exact ⟨h ▸ hi', h⟩
  · exact fun h => h.2

lemma wordRep_mul_columnAlt {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    wordRep n d (h : Equiv.Perm (Fin n)) * columnAlt (d := d) t =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g _
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((h * g : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((h * g : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  congr 1
  calc signC (h : Equiv.Perm (Fin n)) *
      (signC (h : Equiv.Perm (Fin n)) * signC (g : Equiv.Perm (Fin n))) =
      signC (g : Equiv.Perm (Fin n)) *
        (signC (h : Equiv.Perm (Fin n)) * signC (h : Equiv.Perm (Fin n))) := by ring
    _ = signC (g : Equiv.Perm (Fin n)) := by rw [signC_mul_self, mul_one]

lemma wordRep_polytabloid {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (q : columnGroup t) :
    wordRep n (μ.colLen 0) (q : Equiv.Perm (Fin n)) (polytabloid t) =
      signC (q : Equiv.Perm (Fin n)) • polytabloid t := by
  rw [← HananyPuder.W2HP.PartR.columnAlt_row, ← Module.End.mul_apply, wordRep_mul_columnAlt,
    LinearMap.smul_apply]

theorem hom_dominance {N ℓ : ℕ} {μ : YoungDiagram} (t : Tableau N μ) (α : Fin ℓ → ℤ)
    (h : Module.finrank ℂ (Representation.IntertwiningMap (spechtRep t) (permRep N ℓ α)) ≠ 0)
    (k : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin ℓ => (i : ℕ) < k), α i ≤
      ∑ i ∈ Finset.range k, (μ.rowLen i : ℤ) := by
  classical
  obtain ⟨θ, hθ⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mp (Nat.pos_of_ne_zero h)
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  have hp : θ p ≠ 0 := by
    intro h0
    apply hθ
    have key : ∀ (x : WordSpace N (μ.colLen 0))
        (hx : x ∈ Submodule.span ℂ (Set.range fun g : Equiv.Perm (Fin N) =>
          wordRep N (μ.colLen 0) g (polytabloid t))),
        θ ⟨x, hx⟩ = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, rfl⟩ := hy
        change θ (spechtRep t g p) = 0
        rw [θ.isIntertwining, h0, map_zero]
      | zero => exact map_zero θ
      | add y z hy hz ihy ihz =>
        have : (⟨y + z, Submodule.add_mem _ hy hz⟩ : Specht t) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
        rw [this, map_add, ihy, ihz, add_zero]
      | smul a y hy ih =>
        have : (⟨a • y, Submodule.smul_mem _ a hy⟩ : Specht t) = a • ⟨y, hy⟩ := rfl
        rw [this, map_smul, ih, smul_zero]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    exact key x hx
  have hsign : ∀ q : columnGroup t,
      permRep N ℓ α (q : Equiv.Perm (Fin N)) (θ p) = signC (q : Equiv.Perm (Fin N)) • θ p := by
    intro q
    rw [← θ.isIntertwining]
    have : spechtRep t (q : Equiv.Perm (Fin N)) p = signC (q : Equiv.Perm (Fin N)) • p :=
      Subtype.ext (wordRep_polytabloid t q)
    rw [this, map_smul]
  obtain ⟨u, hu⟩ := Function.ne_iff.mp hp
  have hinj : ∀ i j, (t i).val.2 = (t j).val.2 → u.1 i = u.1 j → i = j := by
    intro i j hc he
    by_contra hij
    let q : columnGroup t :=
      ⟨Equiv.swap i j, fun k => Equiv.apply_swap_eq_self (v := fun l => (t l).val.2) hc k⟩
    have h1 := congrFun (hsign q) u
    have hs : signC (q : Equiv.Perm (Fin N)) = -1 := by
      simp [q, signC_def, Equiv.Perm.sign_swap hij]
    have hu' : u.comp (q : Equiv.Perm (Fin N)) = u :=
      Subtype.ext (funext fun k => Equiv.apply_swap_eq_self he k)
    change θ p (u.comp (q : Equiv.Perm (Fin N))) = _ at h1
    rw [hu', hs, Pi.smul_apply, neg_one_smul] at h1
    exact hu (CharZero.eq_neg_self_iff.mp h1)
  rw [sum_alpha_eq α u k]
  have := total_le t u.1 hinj k
  exact_mod_cast this

/-! ## `specht_char_im` -/
lemma trace_im_zero_of_star {N d : ℕ} (V : Submodule ℂ (WordSpace N d))
    (hV : ∀ x ∈ V, star x ∈ V) {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Module.Basis ι ℂ V)
    (hB : ∀ i, star (B i : WordSpace N d) = B i) (f : V →ₗ[ℂ] V)
    (hf : ∀ x : V, star ((f x : V) : WordSpace N d) =
      (f ⟨star (x : WordSpace N d), hV _ x.2⟩ : V)) :
    (LinearMap.trace ℂ V f).im = 0 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ B, Matrix.trace, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Matrix.diag, LinearMap.toMatrix_apply]
  set y := f (B j) with hydef
  have hy : (⟨star (y : WordSpace N d), hV _ y.2⟩ : V) = y := by
    apply Subtype.ext
    change star ((f (B j) : V) : WordSpace N d) = _
    rw [hf (B j)]
    have : (⟨star ((B j : V) : WordSpace N d), hV _ (B j).2⟩ : V) = B j := Subtype.ext (hB j)
    rw [this]
  have hsum : (⟨star (y : WordSpace N d), hV _ y.2⟩ : V) = ∑ k, star (B.repr y k) • B k := by
    apply Subtype.ext
    change star (y : WordSpace N d) = ((∑ k, star (B.repr y k) • B k : V) : WordSpace N d)
    conv_lhs => rw [← B.sum_repr y]
    rw [Submodule.coe_sum, star_sum, Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Submodule.coe_smul, star_smul, hB, Submodule.coe_smul]
  have hrep := congrFun (B.repr_sum_self (fun k => star (B.repr y k))) j
  rw [← hsum, hy] at hrep
  exact Complex.conj_eq_iff_im.mp hrep.symm

theorem specht_char_im {N : ℕ} {μ : YoungDiagram} (t : Tableau N μ) (σ : Equiv.Perm (Fin N)) :
    (LinearMap.trace ℂ (Specht t) (spechtRep t σ)).im = 0 := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℂ
    (Set.range fun g : Equiv.Perm (Fin N) => wordRep N (μ.colLen 0) g (polytabloid t))
  have hV : Submodule.span ℂ (Set.range (Subtype.val : b → WordSpace N (μ.colLen 0))) =
      Specht t := by
    rw [Subtype.range_coe, hspan]
    rfl
  let B : Module.Basis b ℂ (Specht t) := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hV)
  let : Fintype b := FiniteDimensional.fintypeBasisIndex B
  apply trace_im_zero_of_star (Specht t) (fun x hx => cyclic_star _ (polytabloid_real t) hx) B
  · intro i
    have hi : ((B i : Specht t) : WordSpace N (μ.colLen 0)) = i := by
      simp [B, Module.Basis.span_apply]
    rw [hi]
    obtain ⟨g, hg⟩ := hbs i.2
    rw [← hg, wordRep_star, polytabloid_real]
  · intro x
    rfl

end
end StrongConvW2HP.Q289.PartR
end

section
open StrongConv OAI.Saxl
namespace StrongConvW2HP.Q289
noncomputable section
alias specht_char_im := StrongConvW2HP.Q289.PartR.specht_char_im

alias hom_dominance := StrongConvW2HP.Q289.PartR.hom_dominance

alias hom_incl := StrongConvW2HP.Q289.PartR.hom_incl

end
end StrongConvW2HP.Q289
end

section
namespace StrongConvW2HP.Q289.PartG
open StrongConv OAI.Saxl StrongConvW2HP.Q289
noncomputable section
/-- (Part G) For `w ≠ 1` some prefix sum of `α_w` exceeds that of `rows`. -/
theorem dom_w (rows : List ℕ) (w : Equiv.Perm (Fin rows.length)) (hw : w ≠ 1) :
    ∃ k ≤ rows.length,
      ∑ i ∈ Finset.univ.filter (fun i : Fin rows.length => (i : ℕ) < k), (rows.get i : ℤ) <
        ∑ i ∈ Finset.univ.filter (fun i : Fin rows.length => (i : ℕ) < k), alphaW rows w i := by
  classical
  have hne : (Finset.univ.filter fun j : Fin rows.length => w j ≠ j).Nonempty := by
    by_contra h
    apply hw
    ext j
    simp only [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff, Finset.mem_univ,
      true_implies, not_not] at h
    simp [h]
  set j0 := (Finset.univ.filter fun j : Fin rows.length => w j ≠ j).min' hne with hj0
  have hj0mem := Finset.min'_mem _ hne
  rw [← hj0] at hj0mem
  have hj0ne : w j0 ≠ j0 := (Finset.mem_filter.mp hj0mem).2
  have hlt : ∀ i : Fin rows.length, i < j0 → w i = i := by
    intro i hi
    by_contra h
    have := Finset.min'_le (Finset.univ.filter fun j : Fin rows.length => w j ≠ j) i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [← hj0] at this
    exact absurd hi (not_lt.mpr this)
  have hgt : j0 < w j0 := by
    rcases lt_trichotomy (w j0) j0 with h | h | h
    · exfalso
      have := hlt _ h
      exact hj0ne (w.injective this)
    · exact absurd h hj0ne
    · exact h
  have hj0lt := j0.isLt
  refine ⟨j0 + 1, by omega, ?_⟩
  rw [← sub_pos, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single_of_mem j0 (by simp)]
  · simp only [alphaW]
    have : (j0 : ℕ) < (w j0 : ℕ) := hgt
    omega
  · intro b hb hbne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have : b < j0 := by
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hb) with h | h
      · exact h
      · exact absurd (Fin.ext h) hbne
    simp [alphaW, hlt b this]

end
end StrongConvW2HP.Q289.PartG
end

section
open StrongConv OAI.Saxl
namespace StrongConvW2HP.Q289
noncomputable section

end
end StrongConvW2HP.Q289
end

section
namespace StrongConvW2HP.Q289.PartG
open StrongConv OAI.Saxl StrongConvW2HP.Q289
noncomputable section
lemma sum_alphaW (rows : List ℕ) (N : ℕ) (hsum : rows.sum = N)
    (w : Equiv.Perm (Fin rows.length)) : ∑ i, alphaW rows w i = N := by
  simp only [alphaW]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ i : Fin rows.length, ((w i : ℕ) : ℤ) = ∑ i : Fin rows.length, ((i : ℕ) : ℤ) :=
    Equiv.sum_comp w (fun i : Fin rows.length => ((i : ℕ) : ℤ))
  have h2 : ∑ i : Fin rows.length, (rows.get i : ℤ) = N := by
    rw [← hsum, ← Fin.sum_univ_getElem rows]
    push_cast
    rfl
  rw [h1, h2]
  ring

/-- (Part G) James, Theorem 19.2, from the stubs. -/
theorem james (N : ℕ) (rows : List ℕ) (hsorted : rows.SortedGE)
    (hsum : rows.sum = N) (σ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (youngSpace N rows) (youngAct N rows σ) =
      ∑ w : Equiv.Perm (Fin rows.length), ((Equiv.Perm.sign w : ℤ) : ℂ) *
        ((Finset.univ.filter fun f : Fin N → Fin rows.length =>
          (∀ x, f (σ x) = f x) ∧
            ∀ i, ((Finset.univ.filter fun x => f x = i).card : ℤ) =
              (rows.get i : ℤ) - (i : ℕ) + (w i : ℕ)).card : ℂ) := by
  classical
  obtain ⟨μ, t, htr, hrows, hcol⟩ := StrongConvW2HP.Q289.young_specht N rows hsorted hsum
  let c : Equiv.Perm (Fin N) → ℂ := fun σ => LinearMap.trace ℂ (Specht t) (spechtRep t σ)
  have hcardN : Nat.card (Equiv.Perm (Fin N)) = N.factorial := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hNf : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have : Invertible ((Nat.card (Equiv.Perm (Fin N)) : ℂ)) :=
    invertibleOfNonzero (by rw [hcardN]; exact hNf)
  -- (A) orthonormality
  have hA : ∑ g, c g * c g⁻¹ = N.factorial := by
    have := OAI.Saxl.specht_irreducible t
    have := Representation.char_orthonormal (spechtRep t) (spechtRep t)
    rw [if_pos ⟨Representation.Equiv.refl _⟩, hcardN] at this
    have h2 := congrArg (HMul.hMul (N.factorial : ℂ)) this
    rw [← mul_assoc, mul_inv_cancel₀ hNf, one_mul] at h2
    simpa [Representation.character] using h2
  -- (B) Hom dimensions
  let m : Equiv.Perm (Fin rows.length) → ℕ := fun w =>
    Module.finrank ℂ (Representation.IntertwiningMap (spechtRep t)
      (permRep N rows.length (alphaW rows w)))
  have hB : ∀ w, ∑ g, (xi (alphaW rows w) g : ℂ) * c g⁻¹ = N.factorial * m w := by
    intro w
    have := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (spechtRep t)
      (permRep N rows.length (alphaW rows w))
    rw [hcardN] at this
    have h2 := congrArg (HMul.hMul (N.factorial : ℂ)) this
    rw [← mul_assoc, mul_inv_cancel₀ hNf, one_mul] at h2
    simpa [Representation.character, StrongConvW2HP.Q289.permRep_char] using h2
  have hprefix : ∀ k ≤ rows.length,
      ∑ i ∈ Finset.univ.filter (fun i : Fin rows.length => (i : ℕ) < k), (rows.get i : ℤ) =
        ∑ i ∈ Finset.range k, (μ.rowLen i : ℤ) := by
    intro k hk
    rw [Finset.sum_filter]
    simp_rw [hrows]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then (μ.rowLen i : ℤ) else 0),
      ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hm0 : ∀ w, w ≠ 1 → m w = 0 := by
    intro w hw
    by_contra h
    obtain ⟨k, hk, hlt⟩ := dom_w rows w hw
    have := StrongConvW2HP.Q289.hom_dominance t (alphaW rows w) h k
    rw [hprefix k hk] at hlt
    exact absurd this (not_le.mpr hlt)
  have hm1 : 1 ≤ m 1 := by
    apply StrongConvW2HP.Q289.hom_incl t _ _ hcol
    intro i
    simp only [alphaW, Equiv.Perm.coe_one, id]
    rw [hrows i]
    ring
  -- reality
  let r : Equiv.Perm (Fin N) → ℝ := fun g => (c g).re
  have hcr : ∀ g, c g = (r g : ℂ) := fun g =>
    Complex.ext rfl (by simpa using StrongConvW2HP.Q289.specht_char_im t g)
  have hcinv : ∀ g, c g⁻¹ = c g := fun g => StrongConvW2HP.Q289.specht_char_inv t g
  -- real identities
  have hR : ∑ g, r g ^ 2 = N.factorial := by
    have : ((∑ g, r g ^ 2 : ℝ) : ℂ) = ((N.factorial : ℝ) : ℂ) := by
      rw [Complex.ofReal_natCast, ← hA]
      push_cast
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hcinv, hcr, sq]
    exact_mod_cast this
  have hX : ∑ g, (psi N rows g : ℝ) * r g = N.factorial * m 1 := by
    have hXc : ∀ w, ∑ g, (xi (alphaW rows w) g : ℝ) * r g = N.factorial * m w := by
      intro w
      have : ((∑ g, (xi (alphaW rows w) g : ℝ) * r g : ℝ) : ℂ) =
          ((N.factorial * m w : ℝ) : ℂ) := by
        push_cast
        rw [← hB w]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hcinv, hcr]
      exact_mod_cast this
    simp only [psi, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hXc]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin rows.length))]
    · simp
    · intro w _ hw
      simp [hm0 w hw]
    · simp
  have hP : ∑ g, (psi N rows g : ℝ) ^ 2 = N.factorial := by
    have hPz : ∑ g, psi N rows g ^ 2 = N.factorial := by
      calc ∑ g, psi N rows g ^ 2
          = ∑ w : Equiv.Perm (Fin rows.length), ∑ w' : Equiv.Perm (Fin rows.length),
              (Equiv.Perm.sign w : ℤ) * (Equiv.Perm.sign w' : ℤ) *
                ((∑ g, xi (alphaW rows w) g * xi (alphaW rows w') g : ℕ) : ℤ) := by
            have hg : ∀ g, psi N rows g ^ 2 = ∑ w : Equiv.Perm (Fin rows.length),
                ∑ w' : Equiv.Perm (Fin rows.length),
                  (Equiv.Perm.sign w : ℤ) * (Equiv.Perm.sign w' : ℤ) *
                    ((xi (alphaW rows w) g : ℤ) * (xi (alphaW rows w') g : ℤ)) := by
              intro g
              rw [sq, psi, Finset.sum_mul_sum]
              refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
              ring
            rw [Finset.sum_congr rfl fun g _ => hg g, Finset.sum_comm]
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun w' _ => ?_
            rw [Nat.cast_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun g _ => ?_
            push_cast
            ring
        _ = ∑ w : Equiv.Perm (Fin rows.length), ∑ w' : Equiv.Perm (Fin rows.length),
              N.factorial * ((Equiv.Perm.sign w : ℤ) * (Equiv.Perm.sign w' : ℤ) *
                (tables N rows.length (alphaW rows w) (alphaW rows w') : ℤ)) := by
            refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
            rw [StrongConvW2HP.Q289.burnside_tables _ _ (sum_alphaW rows N hsum w)
              (sum_alphaW rows N hsum w')]
            push_cast
            ring
        _ = N.factorial := by
            simp_rw [← Finset.mul_sum]
            rw [StrongConvW2HP.Q289.alternant_tables N rows hsorted hsum, mul_one]
    exact_mod_cast hPz
  -- the norm argument
  have hfpos : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hexp : ∑ g, ((psi N rows g : ℝ) - m 1 * r g) ^ 2 =
      N.factorial * (1 - (m 1 : ℝ) ^ 2) := by
    have : ∀ g, ((psi N rows g : ℝ) - m 1 * r g) ^ 2 =
        (psi N rows g : ℝ) ^ 2 - 2 * m 1 * ((psi N rows g : ℝ) * r g) + (m 1 : ℝ) ^ 2 * r g ^ 2 :=
      fun g => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hP, hX, hR]
    ring
  have hnn : 0 ≤ ∑ g, ((psi N rows g : ℝ) - m 1 * r g) ^ 2 :=
    Finset.sum_nonneg fun g _ => sq_nonneg _
  have hm1eq : m 1 = 1 := by
    rw [hexp] at hnn
    have : (m 1 : ℝ) ^ 2 ≤ 1 := by nlinarith
    have : (m 1 : ℝ) ≤ 1 := by nlinarith
    have : m 1 ≤ 1 := by exact_mod_cast this
    omega
  have hzero : ∑ g, ((psi N rows g : ℝ) - m 1 * r g) ^ 2 = 0 := by
    rw [hexp, hm1eq]; simp
  have hpsi : (psi N rows σ : ℝ) = r σ := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => sq_nonneg _)).mp hzero σ
      (Finset.mem_univ _)
    rw [hm1eq] at this
    simp only [Nat.cast_one, one_mul] at this
    nlinarith [sq_nonneg ((psi N rows σ : ℝ) - r σ)]
  rw [htr σ]
  change c σ = _
  rw [hcr, ← hpsi, Complex.ofReal_intCast]
  unfold psi
  push_cast
  rfl

end
end StrongConvW2HP.Q289.PartG
end

section
open StrongConv OAI.Saxl
namespace StrongConvW2HP.Q289
noncomputable section
alias james := StrongConvW2HP.Q289.PartG.james

end
end StrongConvW2HP.Q289
end

open StrongConv in
theorem solution (N : ℕ) (rows : List ℕ) (hsorted : rows.SortedGE)
    (hsum : rows.sum = N) (σ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (youngSpace N rows) (youngAct N rows σ) =
      ∑ w : Equiv.Perm (Fin rows.length), ((Equiv.Perm.sign w : ℤ) : ℂ) *
        ((Finset.univ.filter fun f : Fin N → Fin rows.length =>
          (∀ x, f (σ x) = f x) ∧
            ∀ i, ((Finset.univ.filter fun x => f x = i).card : ℤ) =
              (rows.get i : ℤ) - (i : ℕ) + (w i : ℕ)).card : ℂ) :=
  StrongConvW2HP.Q289.james N rows hsorted hsum σ

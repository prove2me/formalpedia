-- Prove2me | solution 1 for TwoBQO.embedForAll_wqo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:27.491992+00:00
-- url     : https://prove2.me/submissions/2cbcef59-20b9-4006-bec7-2d44ae0f7d77

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
public import Theorems.Thm_TwoBQO_wellQuasiOrdered
public import Theorems.Thm_TwoBQO_prod
public import Theorems.Thm_TwoBQO_dom_twoBQO
public import Theorems.Thm_P2M_WellQuasiOrdered_sublistForall__eefc84a6e857
public import Theorems.Thm_WellQuasiOrdered_eventuallyRegular

section
@[expose] public section
open Set Preorder
noncomputable section
namespace PairSeq
end PairSeq
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)
private theorem exists_strictMono_of_greedy {P : ℕ → ℕ → Prop}
    (hbuild : ∀ start i : ℕ, ∃ j, start < j ∧ P i j) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, P i (e i) := by
  let e : ℕ → ℕ := fun i =>
    Nat.rec (motive := fun _ => ℕ) (hbuild 0 0).choose
      (fun n prev => (hbuild prev (n + 1)).choose) i
  have he0 : e 0 = (hbuild 0 0).choose := rfl
  have hesucc : ∀ n, e (n + 1) = (hbuild (e n) (n + 1)).choose := fun n => rfl
  have hP0 : P 0 (e 0) := he0 ▸ (hbuild 0 0).choose_spec.2
  have hPsucc : ∀ n, P (n + 1) (e (n + 1)) := fun n =>
    (hesucc n) ▸ (hbuild (e n) (n + 1)).choose_spec.2
  have hlt : ∀ n, e n < e (n + 1) := fun n => (hesucc n) ▸ (hbuild (e n) (n + 1)).choose_spec.1
  refine ⟨e, strictMono_nat_of_lt_succ hlt, fun i => ?_⟩
  cases i with
  | zero => exact hP0
  | succ n => exact hPsucc n
private theorem sublistForall₂_to_embedding {α : Type*} (r : α → α → Prop) (l₁ l₂ : List α)
    (h : List.SublistForall₂ r l₁ l₂) :
    ∃ φ : Fin l₁.length → Fin l₂.length, StrictMono φ ∧ ∀ i, r (l₁.get i) (l₂.get (φ i)) := by
  induction h
  · simp +decide [StrictMono]
  · simp_all +decide only [StrictMono, List.get_eq_getElem, List.length_cons,
      Fin.forall_fin_succ, Fin.not_lt_zero, IsEmpty.forall_iff, true_and, Fin.succ_pos,
      forall_const, Fin.succ_lt_succ_iff, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    obtain ⟨φ, hφ₁, hφ₂⟩ := ‹_›
    use Fin.cons 0 (Fin.succ ∘ φ)
    aesop
  · rename_i l₁ l₂ h ih
    obtain ⟨φ, hφ₁, hφ₂⟩ := ih
    use fun i => Fin.succ (φ i)
    simp_all +decide [StrictMono]
private theorem embed_combine {α : Type*} (r : α → α → Prop) (Fa Fb : ℕ → α) (ka kb : ℕ)
    (ψ : ℕ → ℕ) (hψ_lt : ∀ n, n < ka → ψ n < kb) (hψ_mono : ∀ m n, m < n → n < ka → ψ m < ψ n)
    (hψ_rel : ∀ n, n < ka → r (Fa n) (Fb (ψ n))) (eG : ℕ → ℕ) (heG_mono : StrictMono eG)
    (heG_rel : ∀ i, r (Fa (i + ka)) (Fb (eG i + kb))) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ n, r (Fa n) (Fb (e n)) := by
  refine ⟨fun n => if hn : n < ka then ψ n else eG (n - ka) + kb, ?_, ?_⟩
  · intro m n hmn
    by_cases hm : m < ka <;> by_cases hn : n < ka <;>
      simp +decide only [hm, ↓reduceDIte, hn, add_lt_add_iff_right]
    · exact hψ_mono m n hmn hn
    · linarith [hψ_lt m hm, heG_mono.monotone (Nat.zero_le (n - ka))]
    · linarith
    · exact heG_mono (by omega)
  · grind
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)
namespace TwoBQO
theorem _root_.solution {α : Type*} {r : α → α → Prop} [IsPreorder α r] (hr : TwoBQO r) :
    WellQuasiOrdered (EmbedForAll r) := by
  intro F
  have hreg : ∀ n, ∃ k, IsRegularSeq r fun i => F n (i + k) :=
    fun n => hr.wellQuasiOrdered.eventuallyRegular r (F n)
  choose kk hkk using hreg
  set G : ℕ → ℕ → α := fun n i => F n (i + kk n) with hG_def
  set w : ℕ → List α := fun n => (List.range (kk n)).map (F n) with hw_def
  have hw_len : ∀ n, (w n).length = kk n := fun n => by simp [hw_def]
  have hw_get : ∀ n (i : ℕ) (h : i < (w n).length), (w n)[i] = F n i := fun n i h => by
    simp [hw_def, List.getElem_map, List.getElem_range]
  have hwqo_list : WellQuasiOrdered (List.SublistForall₂ r) := hr.wellQuasiOrdered.sublistForall₂
  have hdom_wqo : WellQuasiOrdered (DomOrder r) := hr.dom_twoBQO
  set S : ℕ → Set α := fun n => {x : α | ∃ i, r x (G n i)} with hS_def
  have hprod_wqo : WellQuasiOrdered
      (fun p q : List α × Set α => List.SublistForall₂ r p.1 q.1 ∧ DomOrder r p.2 q.2) :=
    WellQuasiOrdered.prod hwqo_list hdom_wqo
  obtain ⟨a, b, hab, hwgood, hSgood⟩ := hprod_wqo fun n => (w n, S n)
  have hpt : ∀ i, ∃ j, r (G a i) (G b j) := fun i => by
    obtain ⟨y, ⟨j, hy_mem⟩, hy_rel⟩ := hSgood (G a i) ⟨i, refl (G a i)⟩
    exact ⟨j, _root_.trans hy_rel hy_mem⟩
  have hbuild : ∀ start i : ℕ, ∃ j, start < j ∧ r (G a i) (G b j) := fun start i => by
    obtain ⟨j0, hj0⟩ := hpt i
    obtain ⟨j, hmem, hgt⟩ := Set.Infinite.exists_gt (hkk b j0) start
    exact ⟨j, hgt, IsTrans.trans _ _ _ hj0 hmem⟩
  obtain ⟨eG, heG_mono, heG_rel⟩ := exists_strictMono_of_greedy hbuild
  obtain ⟨φ, hφ_mono, hφ_rel⟩ := sublistForall₂_to_embedding r (w a) (w b) hwgood
  refine ⟨a, b, hab, ?_⟩
  refine embed_combine r (F a) (F b) (kk a) (kk b)
    (fun n => if h : n < kk a then (φ (Fin.cast (hw_len a).symm ⟨n, h⟩)).val else 0)
    ?_ ?_ ?_ eG heG_mono ?_
  · -- bound: the head map stays below `kk b`
    intro n hn
    simp only [dif_pos hn]
    have h := (φ (Fin.cast (hw_len a).symm ⟨n, hn⟩)).isLt
    have hl := hw_len b
    omega
  · -- monotonicity of the head map
    intro m n hmn hn
    have hm : m < kk a := lt_trans hmn hn
    simp only [dif_pos hm, dif_pos hn]
    have h := hφ_mono (a := Fin.cast (hw_len a).symm ⟨m, hm⟩)
      (b := Fin.cast (hw_len a).symm ⟨n, hn⟩) (by simpa using hmn)
    simpa using h
  · -- the head map witnesses `r`
    intro n hn
    simp only [dif_pos hn]
    have h := hφ_rel (Fin.cast (hw_len a).symm ⟨n, hn⟩)
    simpa [hw_def, List.get_eq_getElem, List.getElem_map, List.getElem_range,
      Fin.val_cast] using h
  · -- the tail map witnesses `r` (definitionally `G`)
    exact heG_rel
end TwoBQO

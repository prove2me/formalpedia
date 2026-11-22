-- Prove2me | solution 1 for OfflineStochMatch.Attenuation.safe_relaxed_integral
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:40:24.182542+00:00
-- url     : https://prove2.me/submissions/2c040e3d-2b7c-4ad7-be57-3cbad79c2d75

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting
import Definitions.Def_OfflineStochMatch_Attenuation_SideProb

open OfflineStochMatch.Attenuation

section Helpers

private lemma disjoint_otherIncident {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (e : E) (u v : V) (huv : G.ends e = s(u, v)) :
    Disjoint (otherIncident G e u) (otherIncident G e v) := by
  have hne : u ≠ v := by
    intro h
    have hdiag : (G.ends e).IsDiag := by
      rw [huv, h]
      simp
    exact G.loopless e hdiag
  have hsym : ∀ z : Sym2 V, u ∈ z → v ∈ z → z = s(u, v) := by
    intro z
    induction z using Sym2.ind with
    | _ a b =>
      intro hu hv
      simp only [Sym2.mem_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (hne rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hne rfl).elim
  rw [Finset.disjoint_left]
  intro f hfu hfv
  simp only [otherIncident, incident, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
    true_and] at hfu hfv
  have hfeq : G.ends f = G.ends e := (hsym (G.ends f) hfu.2 hfv.2).trans huv.symm
  exact hfu.1 (hG hfeq)

private lemma sideOK_congr {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (e : E) (r : V)
    {B₁ B₂ Y₁ Y₂ A₁ A₂ P₁ P₂ : E → Bool}
    (h : ∀ f ∈ otherIncident G e r,
      B₁ f = B₂ f ∧ Y₁ f = Y₂ f ∧ A₁ f = A₂ f ∧ P₁ f = P₂ f) :
    SideOK G t e r B₁ Y₁ A₁ P₁ ↔ SideOK G t e r B₂ Y₂ A₂ P₂ := by
  unfold SideOK
  have h1 :
      (∀ f ∈ otherIncident G e r, ¬ (B₁ f = true ∧ Y₁ f = true ∧ A₁ f = true ∧ P₁ f = true)) ↔
      (∀ f ∈ otherIncident G e r, ¬ (B₂ f = true ∧ Y₂ f = true ∧ A₂ f = true ∧ P₂ f = true)) := by
    constructor <;> intro h' f hf
    · obtain ⟨hB, hY, hA, hP⟩ := h f hf
      rw [← hB, ← hY, ← hA, ← hP]
      exact h' f hf
    · obtain ⟨hB, hY, hA, hP⟩ := h f hf
      rw [hB, hY, hA, hP]
      exact h' f hf
  have h2 :
      (otherIncident G e r).filter (fun f => B₁ f = true ∧ Y₁ f = true ∧ A₁ f = true) =
      (otherIncident G e r).filter (fun f => B₂ f = true ∧ Y₂ f = true ∧ A₂ f = true) := by
    refine Finset.filter_congr ?_
    intro f hf
    obtain ⟨hB, hY, hA, _⟩ := h f hf
    simp [hB, hY, hA]
  rw [h1, h2]

private lemma disjoint_product_sum {E α : Type*} [Fintype E] [DecidableEq E]
    [Fintype α] [Inhabited α]
    (w : E → α → ℝ) (hw : ∀ f, ∑ a : α, w f a = 1)
    (S₁ S₂ : Finset E) (hdisj : Disjoint S₁ S₂)
    (g₁ g₂ : (E → α) → ℝ)
    (hg₁ : ∀ ω₁ ω₂, (∀ f ∈ S₁, ω₁ f = ω₂ f) → g₁ ω₁ = g₁ ω₂)
    (hg₂ : ∀ ω₁ ω₂, (∀ f ∈ S₂, ω₁ f = ω₂ f) → g₂ ω₁ = g₂ ω₂) :
    (∑ ω : E → α, (∏ f, w f (ω f)) * g₁ ω) * (∑ ω : E → α, (∏ f, w f (ω f)) * g₂ ω) =
      ∑ ω : E → α, (∏ f, w f (ω f)) * (g₁ ω * g₂ ω) := by
  let eSplit : (E → α) ≃ ({f : E // f ∈ S₁} → α) × ({f : E // f ∉ S₁} → α) :=
    Equiv.piEquivPiSubtypeProd (fun f : E => f ∈ S₁) (fun _ => α)
  let W₁ : ({f : E // f ∈ S₁} → α) → ℝ := fun ω₁ => ∏ f, w f.1 (ω₁ f)
  let W₂ : ({f : E // f ∉ S₁} → α) → ℝ := fun ω₂ => ∏ f, w f.1 (ω₂ f)
  let G₁ : ({f : E // f ∈ S₁} → α) → ℝ := fun ω₁ => g₁ (eSplit.symm (ω₁, fun _ => default))
  let G₂ : ({f : E // f ∉ S₁} → α) → ℝ := fun ω₂ => g₂ (eSplit.symm (fun _ => default, ω₂))
  have hprod : ∀ (ω₁ : {f : E // f ∈ S₁} → α) (ω₂ : {f : E // f ∉ S₁} → α),
      ∏ f : E, w f (eSplit.symm (ω₁, ω₂) f) = W₁ ω₁ * W₂ ω₂ := by
    intro ω₁ ω₂
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun f : E => f ∈ S₁)
      (fun f => w f (eSplit.symm (ω₁, ω₂) f))]
    congr 1
    · refine Finset.prod_congr (by ext; simp) ?_
      intro f _
      simp [eSplit, f.2]
    · refine Finset.prod_congr (by ext; simp) ?_
      intro f _
      simp [eSplit, f.2]
  have hW₁ : ∑ ω₁, W₁ ω₁ = 1 := by
    change ∑ ω₁ : {f : E // f ∈ S₁} → α, ∏ f, w f.1 (ω₁ f) = 1
    rw [← Fintype.prod_sum]
    simp [hw]
  have hW₂ : ∑ ω₂, W₂ ω₂ = 1 := by
    change ∑ ω₂ : {f : E // f ∉ S₁} → α, ∏ f, w f.1 (ω₂ f) = 1
    rw [← Fintype.prod_sum]
    simp [hw]
  have hG₁ : ∀ ω₁ ω₂, g₁ (eSplit.symm (ω₁, ω₂)) = G₁ ω₁ := by
    intro ω₁ ω₂
    apply hg₁
    intro f hf
    simp [eSplit, hf]
  have hG₂ : ∀ ω₁ ω₂, g₂ (eSplit.symm (ω₁, ω₂)) = G₂ ω₂ := by
    intro ω₁ ω₂
    apply hg₂
    intro f hf
    have hf' : f ∉ S₁ := Finset.disjoint_right.mp hdisj hf
    simp [eSplit, hf']
  have hs1 : ∑ ω : E → α, (∏ f, w f (ω f)) * g₁ ω = ∑ ω₁, W₁ ω₁ * G₁ ω₁ := by
    rw [← Equiv.sum_comp eSplit.symm, Fintype.sum_prod_type]
    calc
      ∑ ω₁, ∑ ω₂, (∏ f, w f (eSplit.symm (ω₁, ω₂) f)) * g₁ (eSplit.symm (ω₁, ω₂))
          = ∑ ω₁, ∑ ω₂, (W₁ ω₁ * G₁ ω₁) * W₂ ω₂ := by
            refine Finset.sum_congr rfl fun ω₁ _ => Finset.sum_congr rfl fun ω₂ _ => ?_
            rw [hprod, hG₁]
            ring
      _ = ∑ ω₁, (W₁ ω₁ * G₁ ω₁) * ∑ ω₂, W₂ ω₂ := by
            refine Finset.sum_congr rfl fun ω₁ _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ ω₁, W₁ ω₁ * G₁ ω₁ := by simp [hW₂]
  have hs2 : ∑ ω : E → α, (∏ f, w f (ω f)) * g₂ ω = ∑ ω₂, W₂ ω₂ * G₂ ω₂ := by
    rw [← Equiv.sum_comp eSplit.symm, Fintype.sum_prod_type]
    calc
      ∑ ω₁, ∑ ω₂, (∏ f, w f (eSplit.symm (ω₁, ω₂) f)) * g₂ (eSplit.symm (ω₁, ω₂))
          = ∑ ω₁, W₁ ω₁ * ∑ ω₂, W₂ ω₂ * G₂ ω₂ := by
            refine Finset.sum_congr rfl fun ω₁ _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun ω₂ _ => ?_
            rw [hprod, hG₂]
            ring
      _ = (∑ ω₁, W₁ ω₁) * ∑ ω₂, W₂ ω₂ * G₂ ω₂ := (Finset.sum_mul _ _ _).symm
      _ = ∑ ω₂, W₂ ω₂ * G₂ ω₂ := by simp [hW₁]
  have hs12 : ∑ ω : E → α, (∏ f, w f (ω f)) * (g₁ ω * g₂ ω) =
      (∑ ω₁, W₁ ω₁ * G₁ ω₁) * (∑ ω₂, W₂ ω₂ * G₂ ω₂) := by
    rw [← Equiv.sum_comp eSplit.symm, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ω₁ _ => Finset.sum_congr rfl fun ω₂ _ => ?_
    rw [hprod, hG₁, hG₂]
    ring
  rw [hs1, hs2, hs12]

private def quadEquiv (E : Type*) :
    (E → Bool) × (E → Bool) × (E → Bool) × (E → Bool) ≃ (E → Bool × Bool × Bool × Bool) where
  toFun := fun ⟨B, Y, A, P⟩ f => (B f, Y f, A f, P f)
  invFun := fun ω =>
    (fun f => (ω f).1, fun f => (ω f).2.1, fun f => (ω f).2.2.1, fun f => (ω f).2.2.2)
  left_inv := by rintro ⟨B, Y, A, P⟩; rfl
  right_inv := by intro ω; funext f; rfl

private lemma quad_sum_eq {E : Type*} [Fintype E] [DecidableEq E]
    (q₁ q₂ q₃ q₄ : E → ℝ) (g : (E → Bool) → (E → Bool) → (E → Bool) → (E → Bool) → ℝ) :
    ∑ B : E → Bool, ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
        coinWeight q₁ B * coinWeight q₂ Y * coinWeight q₃ A * coinWeight q₄ P * g B Y A P =
      ∑ ω : E → Bool × Bool × Bool × Bool,
        (∏ f : E, bern (q₁ f) (ω f).1 * bern (q₂ f) (ω f).2.1 *
          bern (q₃ f) (ω f).2.2.1 * bern (q₄ f) (ω f).2.2.2) *
          g (fun f => (ω f).1) (fun f => (ω f).2.1)
            (fun f => (ω f).2.2.1) (fun f => (ω f).2.2.2) := by
  rw [← Equiv.sum_comp (quadEquiv E)]
  simp only [Fintype.sum_prod_type, quadEquiv, Equiv.coe_fn_mk, coinWeight,
    ← Finset.prod_mul_distrib]

open Classical in
private lemma sideProb_mul_sideProb {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ) (e : E) (u v : V) (huv : G.ends e = s(u, v))
    (x : ℝ) :
    sideProb G p t y aT e u x * sideProb G p t y aT e v x =
      ∑ B : E → Bool, coinWeight (fun _ => x) B *
        ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
          coinWeight y Y * coinWeight (attProb aT p y) A * coinWeight p P *
            (if SideOK G t e u B Y A P ∧ SideOK G t e v B Y A P then 1 else 0) := by
  unfold sideProb
  rw [quad_sum_eq, quad_sum_eq]
  let w : E → Bool × Bool × Bool × Bool → ℝ := fun f c =>
    bern x c.1 * bern (y f) c.2.1 * bern (attProb aT p y f) c.2.2.1 * bern (p f) c.2.2.2
  have hw : ∀ f : E, ∑ c : Bool × Bool × Bool × Bool, w f c = 1 := by
    intro f
    simp only [w, Fintype.sum_prod_type, Fintype.sum_bool, bern, ↓reduceIte, Bool.false_eq_true]
    ring
  let g₁ : (E → Bool × Bool × Bool × Bool) → ℝ := fun ω =>
    if SideOK G t e u (fun f => (ω f).1) (fun f => (ω f).2.1)
        (fun f => (ω f).2.2.1) (fun f => (ω f).2.2.2) then 1 else 0
  let g₂ : (E → Bool × Bool × Bool × Bool) → ℝ := fun ω =>
    if SideOK G t e v (fun f => (ω f).1) (fun f => (ω f).2.1)
        (fun f => (ω f).2.2.1) (fun f => (ω f).2.2.2) then 1 else 0
  have hg₁ : ∀ ω₁ ω₂, (∀ f ∈ otherIncident G e u, ω₁ f = ω₂ f) → g₁ ω₁ = g₁ ω₂ := by
    intro ω₁ ω₂ h
    have hiff := sideOK_congr G t e u (fun f hf => by
      have hfeq := h f hf
      exact ⟨congrArg Prod.fst hfeq,
        congrArg (fun c => c.2.1) hfeq,
        congrArg (fun c => c.2.2.1) hfeq,
        congrArg (fun c => c.2.2.2) hfeq⟩)
    simp only [g₁, hiff]
  have hg₂ : ∀ ω₁ ω₂, (∀ f ∈ otherIncident G e v, ω₁ f = ω₂ f) → g₂ ω₁ = g₂ ω₂ := by
    intro ω₁ ω₂ h
    have hiff := sideOK_congr G t e v (fun f hf => by
      have hfeq := h f hf
      exact ⟨congrArg Prod.fst hfeq,
        congrArg (fun c => c.2.1) hfeq,
        congrArg (fun c => c.2.2.1) hfeq,
        congrArg (fun c => c.2.2.2) hfeq⟩)
    simp only [g₂, hiff]
  have hfact := disjoint_product_sum w hw (otherIncident G e u) (otherIncident G e v)
    (disjoint_otherIncident G hG e u v huv) g₁ g₂ hg₁ hg₂
  change (∑ ω, (∏ f, w f (ω f)) * g₁ ω) * (∑ ω, (∏ f, w f (ω f)) * g₂ ω) = _
  rw [hfact]
  have hind : ∀ ω : E → Bool × Bool × Bool × Bool,
      g₁ ω * g₂ ω =
      if SideOK G t e u (fun f => (ω f).1) (fun f => (ω f).2.1)
            (fun f => (ω f).2.2.1) (fun f => (ω f).2.2.2) ∧
         SideOK G t e v (fun f => (ω f).1) (fun f => (ω f).2.1)
            (fun f => (ω f).2.2.1) (fun f => (ω f).2.2.2) then 1 else 0 := by
    intro ω
    dsimp only [g₁, g₂]
    by_cases hu : SideOK G t e u (fun f => (ω f).1) (fun f => (ω f).2.1)
        (fun f => (ω f).2.2.1) (fun f => (ω f).2.2.2) <;>
    by_cases hv : SideOK G t e v (fun f => (ω f).1) (fun f => (ω f).2.1)
        (fun f => (ω f).2.2.1) (fun f => (ω f).2.2.2) <;>
    simp [hu, hv]
  simp_rw [hind]
  dsimp only [w]
  rw [← quad_sum_eq (fun _ => x) y (attProb aT p y) p
    (fun B Y A P => if SideOK G t e u B Y A P ∧ SideOK G t e v B Y A P then 1 else 0)]
  refine Finset.sum_congr rfl fun B _ => ?_
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun A _ =>
    Finset.sum_congr rfl fun P _ => by ring

private def boolFunEquiv {E : Type*} [Fintype E] [DecidableEq E] (e : E) :
    (E → Bool) ≃ {S : Finset E // S ∈ (Finset.univ.erase e).powerset} × Bool where
  toFun B :=
    (⟨(Finset.univ.erase e).filter (fun f => B f = true),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩, B e)
  invFun p := fun f => if f = e then p.2 else decide (f ∈ p.1.1)
  left_inv B := by
    funext f
    by_cases hf : f = e
    · subst hf; simp
    · cases hBf : B f <;> simp [hf, hBf]
  right_inv := by
    rintro ⟨⟨S, hS⟩, b⟩
    refine Prod.ext ?_ (by simp)
    apply Subtype.ext
    ext f
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    by_cases hf : f = e
    · have heS : e ∉ S := fun h => (Finset.mem_erase.mp (Finset.mem_powerset.mp hS h)).1 rfl
      rw [hf]
      simp [heS]
    · simp [hf]

private lemma sum_coinWeight_const_mul {E : Type*} [Fintype E] [DecidableEq E]
    (e : E) (F : (E → Bool) → ℝ)
    (hF : ∀ B₁ B₂, (∀ f ≠ e, B₁ f = B₂ f) → F B₁ = F B₂) (x : ℝ) :
    ∑ B : E → Bool, coinWeight (fun _ => x) B * F B =
      ∑ S ∈ (Finset.univ.erase e).powerset,
        x ^ S.card * (1 - x) ^ ((Finset.univ.erase e) \ S).card * F (fun f => decide (f ∈ S)) := by
  have hcw : ∀ (S : Finset E) (hS : S ⊆ Finset.univ.erase e) (b : Bool),
      coinWeight (fun _ => x) (fun f => if f = e then b else decide (f ∈ S)) =
        bern x b * (x ^ S.card * (1 - x) ^ ((Finset.univ.erase e) \ S).card) := by
    intro S hS b
    unfold coinWeight
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
    simp only [↓reduceIte]
    congr 1
    have hpart : Finset.univ.erase e = S ∪ ((Finset.univ.erase e) \ S) :=
      (Finset.union_sdiff_of_subset hS).symm
    conv_lhs => rw [hpart]
    rw [Finset.prod_union disjoint_sdiff_self_right]
    congr 1
    · calc
        ∏ f ∈ S, bern x (if f = e then b else decide (f ∈ S))
            = ∏ _f ∈ S, x := by
              refine Finset.prod_congr rfl ?_
              intro f hf
              have hfe : f ≠ e := (Finset.mem_erase.mp (hS hf)).1
              simp [hfe, hf, bern]
        _ = x ^ S.card := by simp
    · calc
        ∏ f ∈ (Finset.univ.erase e) \ S, bern x (if f = e then b else decide (f ∈ S))
            = ∏ _f ∈ (Finset.univ.erase e) \ S, (1 - x) := by
              refine Finset.prod_congr rfl ?_
              intro f hf
              rw [Finset.mem_sdiff] at hf
              have hfe : f ≠ e := (Finset.mem_erase.mp hf.1).1
              simp [hfe, hf.2, bern]
        _ = (1 - x) ^ ((Finset.univ.erase e) \ S).card := by simp
  rw [← Equiv.sum_comp (boolFunEquiv e).symm, Fintype.sum_prod_type]
  have hstep :
      ∑ S : {S : Finset E // S ∈ (Finset.univ.erase e).powerset},
        ∑ b : Bool,
          coinWeight (fun _ => x) ((boolFunEquiv e).symm (S, b)) *
            F ((boolFunEquiv e).symm (S, b)) =
      ∑ S : {S : Finset E // S ∈ (Finset.univ.erase e).powerset},
        x ^ S.1.card * (1 - x) ^ ((Finset.univ.erase e) \ S.1).card *
          F (fun f => decide (f ∈ S.1)) := by
    refine Finset.sum_congr rfl fun S _ => ?_
    have hS : S.1 ⊆ Finset.univ.erase e := Finset.mem_powerset.mp S.2
    have hF_eq : ∀ b : Bool,
        F ((boolFunEquiv e).symm (S, b)) = F (fun f => decide (f ∈ S.1)) := by
      intro b
      apply hF
      intro f hf
      simp [boolFunEquiv, hf]
    simp_rw [hF_eq]
    have hcw' : ∀ b : Bool,
        coinWeight (fun _ => x) ((boolFunEquiv e).symm (S, b)) =
          bern x b * (x ^ S.1.card * (1 - x) ^ ((Finset.univ.erase e) \ S.1).card) :=
      fun b => hcw S.1 hS b
    simp only [hcw', Fintype.sum_bool, bern, ↓reduceIte, Bool.false_eq_true]
    ring
  rw [hstep, Finset.sum_coe_sort (Finset.univ.erase e).powerset
    (fun S => x ^ S.card * (1 - x) ^ ((Finset.univ.erase e) \ S).card *
      F (fun f => decide (f ∈ S)))]

private lemma integral_pow_mul_one_sub_pow : ∀ (m k : ℕ),
    ∫ x in (0 : ℝ)..1, x ^ k * (1 - x) ^ m =
      ((k.factorial : ℝ) * (m.factorial : ℝ)) / ((k + m + 1).factorial : ℝ)
  | 0, k => by
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [integral_pow]
    have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
    field_simp
  | m + 1, k => by
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => t ^ (k + 1) * (1 - t) ^ (m + 1))
          (((k + 1 : ℝ) * (x ^ k * (1 - x) ^ (m + 1))) -
            ((m + 1 : ℝ) * (x ^ (k + 1) * (1 - x) ^ m))) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => t ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * x ^ k) x :=
        hasDerivAt_pow (k + 1) x
      have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x :=
        (hasDerivAt_id x).const_sub (1 : ℝ)
      have h2 : HasDerivAt (fun t : ℝ => (1 - t) ^ (m + 1))
          (((m + 1 : ℕ) : ℝ) * (1 - x) ^ m * (-1)) x :=
        (hasDerivAt_pow (m + 1) (1 - x)).comp x hsub
      have hmul : HasDerivAt (fun t : ℝ => t ^ (k + 1) * (1 - t) ^ (m + 1))
          ((((k + 1 : ℕ) : ℝ) * x ^ k) * (1 - x) ^ (m + 1) +
            x ^ (k + 1) * (((m + 1 : ℕ) : ℝ) * (1 - x) ^ m * (-1))) x :=
        h1.mul h2
      exact hmul.congr_deriv (by push_cast; ring)
    have hint1 : IntervalIntegrable
        (fun x : ℝ => (k + 1 : ℝ) * (x ^ k * (1 - x) ^ (m + 1))) MeasureTheory.volume 0 1 :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have hint2 : IntervalIntegrable
        (fun x : ℝ => (m + 1 : ℝ) * (x ^ (k + 1) * (1 - x) ^ m)) MeasureTheory.volume 0 1 :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.sub hint2)
    simp only [sub_self, zero_pow (Nat.succ_ne_zero m), mul_zero,
      zero_pow (Nat.succ_ne_zero k), zero_mul, sub_zero] at hftc
    rw [intervalIntegral.integral_sub hint1 hint2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
    have hih := integral_pow_mul_one_sub_pow m (k + 1)
    have hstep : (k + 1 : ℝ) * (∫ x in (0 : ℝ)..1, x ^ k * (1 - x) ^ (m + 1)) =
        (m + 1 : ℝ) * (∫ x in (0 : ℝ)..1, x ^ (k + 1) * (1 - x) ^ m) := by linarith
    rw [hih] at hstep
    have heq : k + 1 + m + 1 = k + (m + 1) + 1 := by omega
    rw [heq] at hstep
    have hk1 : (k + 1 : ℝ) ≠ 0 := by positivity
    have hfac : (((k + (m + 1) + 1).factorial : ℝ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hcalc : (k + 1 : ℝ) * (∫ x in (0 : ℝ)..1, x ^ k * (1 - x) ^ (m + 1)) =
        (k + 1 : ℝ) * (((k.factorial : ℝ) * ((m + 1).factorial : ℝ)) /
          ((k + (m + 1) + 1).factorial : ℝ)) := by
      rw [hstep, Nat.factorial_succ k, Nat.factorial_succ m]
      push_cast
      ring
    exact mul_left_cancel₀ hk1 hcalc

private lemma card_equiv_of_card_eq {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (h : Fintype.card α = Fintype.card β) :
    Fintype.card (α ≃ β) = (Fintype.card α).factorial := by
  let e : α ≃ β := Fintype.equivOfCardEq h
  have hcongr : (α ≃ β) ≃ Equiv.Perm α :=
    { toFun := fun f => f.trans e.symm
      invFun := fun g => g.trans e
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp }
  rw [Fintype.card_congr hcongr, Fintype.card_perm]

private lemma card_fin_lt (n : ℕ) (k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  have e : Fin k ≃ {i : Fin n // i.val < k} :=
    { toFun := fun j => ⟨⟨j.val, lt_of_lt_of_le j.isLt hk⟩, j.isLt⟩
      invFun := fun i => ⟨i.1.val, i.2⟩
      left_inv := fun j => by ext; rfl
      right_inv := fun i => by ext; rfl }
  rw [← Fintype.card_subtype, ← Fintype.card_congr e, Fintype.card_fin]

private lemma card_perm_beforeSet {E : Type*} [Fintype E] [DecidableEq E]
    (e : E) (S : Finset E) (hS : S ⊆ Finset.univ.erase e) :
    (Finset.univ.filter (fun σ : E ≃ Fin (Fintype.card E) =>
      Finset.univ.filter (fun f => σ f < σ e) = S)).card =
      S.card.factorial * ((Finset.univ.erase e) \ S).card.factorial := by
  set n := Fintype.card E with hn_def
  set k := S.card with hk_def
  set T := (Finset.univ.erase e) \ S with hT_def
  have hcard_erase : (Finset.univ.erase e).card + 1 = n := by
    rw [Finset.card_erase_add_one (Finset.mem_univ e), Finset.card_univ, hn_def]
  have hcard_ST : k + T.card = (Finset.univ.erase e).card := by
    rw [add_comm]
    exact Finset.card_sdiff_add_card_eq_card hS
  have hk : k < n := by omega
  have heS : e ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
  have heT : e ∉ T := fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl
  set L : Finset (Fin n) := Finset.univ.filter (fun i => i.val < k)
  set R : Finset (Fin n) := Finset.univ.filter (fun i => k < i.val)
  have hL_card : L.card = k := card_fin_lt n k (le_of_lt hk)
  have hR_card : R.card = T.card := by
    have hdisj1 : Disjoint L R := by
      rw [Finset.disjoint_left]
      intro i hiL hiR
      simp only [L, R, Finset.mem_filter, Finset.mem_univ, true_and] at hiL hiR
      omega
    have hk_not_LR : (⟨k, hk⟩ : Fin n) ∉ L ∪ R := by
      simp [L, R]
    have hunion : insert (⟨k, hk⟩ : Fin n) (L ∪ R) = Finset.univ := by
      ext i
      simp only [Finset.mem_insert, Finset.mem_union, L, R, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      rcases lt_trichotomy i.val k with hlt | heq | hgt
      · exact Or.inr (Or.inl hlt)
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr (Or.inr hgt)
    have htot := congrArg Finset.card hunion
    rw [Finset.card_insert_of_notMem hk_not_LR, Finset.card_union_of_disjoint hdisj1,
      Finset.card_univ, Fintype.card_fin, hL_card] at htot
    omega
  have hσe : ∀ σ : E ≃ Fin n, Finset.univ.filter (fun f => σ f < σ e) = S →
      σ e = ⟨k, hk⟩ := by
    intro σ hσ
    apply Fin.ext
    have hbi : {f : E // σ f < σ e} ≃ {i : Fin n // i < σ e} :=
      { toFun := fun f => ⟨σ f.1, f.2⟩
        invFun := fun i => ⟨σ.symm i.1, by simpa using i.2⟩
        left_inv := fun f => by ext; simp
        right_inv := fun i => by ext; simp }
    have h1 : S.card = (Finset.univ.filter (fun i : Fin n => i < σ e)).card := by
      rw [← hσ, ← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr hbi
    have h2 : (Finset.univ.filter (fun i : Fin n => i < σ e)).card = (σ e).val :=
      card_fin_lt n (σ e).val (le_of_lt (σ e).isLt)
    dsimp only
    omega
  let equivSplit :
      {σ : E ≃ Fin n // Finset.univ.filter (fun f => σ f < σ e) = S} ≃
        (↥S ≃ ↥L) × (↥T ≃ ↥R) :=
    { toFun := fun ⟨σ, hσ⟩ =>
        have h_e : σ e = ⟨k, hk⟩ := hσe σ hσ
        have hmemS : ∀ f, f ∈ S ↔ (σ f).val < k := by
          intro f
          rw [← hσ, Finset.mem_filter]
          simp [Fin.lt_def, h_e]
        have hmemT : ∀ f, f ∈ T ↔ k < (σ f).val := by
          intro f
          simp only [T, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, hmemS]
          constructor
          · rintro ⟨hfe, hnotlt⟩
            have hne : (σ f).val ≠ k := by
              intro heq
              apply hfe
              apply σ.injective
              rw [h_e]
              exact Fin.ext heq
            omega
          · intro hgt
            refine ⟨?_, by omega⟩
            intro hfe
            subst hfe
            rw [h_e] at hgt
            dsimp only at hgt
            omega
        ( { toFun := fun f => ⟨σ f.1, by simp [L, (hmemS f.1).mp f.2]⟩
            invFun := fun i =>
              ⟨σ.symm i.1, (hmemS (σ.symm i.1)).mpr (by
                have hi : i.1 ∈ L := i.2
                simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hi
                simpa using hi)⟩
            left_inv := fun f => by ext; simp
            right_inv := fun i => by ext; simp },
          { toFun := fun f => ⟨σ f.1, by simp [R, (hmemT f.1).mp f.2]⟩
            invFun := fun i =>
              ⟨σ.symm i.1, (hmemT (σ.symm i.1)).mpr (by
                have hi : i.1 ∈ R := i.2
                simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hi
                simpa using hi)⟩
            left_inv := fun f => by ext; simp
            right_inv := fun i => by ext; simp } )
      invFun := fun ⟨eL, eR⟩ =>
        let σ : E ≃ Fin n :=
          { toFun := fun f =>
              if hfS : f ∈ S then (eL ⟨f, hfS⟩).1
              else if hfT : f ∈ T then (eR ⟨f, hfT⟩).1
              else ⟨k, hk⟩
            invFun := fun i =>
              if hiL : i ∈ L then (eL.symm ⟨i, hiL⟩).1
              else if hiR : i ∈ R then (eR.symm ⟨i, hiR⟩).1
              else e
            left_inv := fun f => by
              by_cases hfS : f ∈ S
              · have h1 : (eL ⟨f, hfS⟩).1 ∈ L := (eL ⟨f, hfS⟩).2
                simp [hfS, h1]
              · by_cases hfT : f ∈ T
                · have h1 : (eR ⟨f, hfT⟩).1 ∈ R := (eR ⟨f, hfT⟩).2
                  have hnotL : (eR ⟨f, hfT⟩).1 ∉ L := by
                    simp only [L, R, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
                    omega
                  simp [hfS, hfT, h1, hnotL]
                · have hfe : f = e := by
                    by_contra hne
                    exact hfT (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_univ f⟩, hfS⟩)
                  have hnotL : (⟨k, hk⟩ : Fin n) ∉ L := by simp [L]
                  have hnotR : (⟨k, hk⟩ : Fin n) ∉ R := by simp [R]
                  subst hfe
                  simp [heS, heT, hnotL, hnotR]
            right_inv := fun i => by
              by_cases hiL : i ∈ L
              · have h1 : (eL.symm ⟨i, hiL⟩).1 ∈ S := (eL.symm ⟨i, hiL⟩).2
                simp [hiL, h1]
              · by_cases hiR : i ∈ R
                · have h1 : (eR.symm ⟨i, hiR⟩).1 ∈ T := (eR.symm ⟨i, hiR⟩).2
                  have hnotS : (eR.symm ⟨i, hiR⟩).1 ∉ S := (Finset.mem_sdiff.mp h1).2
                  simp [hiL, hiR, h1, hnotS]
                · have hieq : i = ⟨k, hk⟩ := by
                    simp only [L, R, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hiL hiR
                    exact Fin.ext (by dsimp only; omega)
                  have hnotL : (⟨k, hk⟩ : Fin n) ∉ L := by simp [L]
                  have hnotR : (⟨k, hk⟩ : Fin n) ∉ R := by simp [R]
                  subst hieq
                  simp [hnotL, hnotR, heS, heT] }
        have hσ_eq : Finset.univ.filter (fun f => σ f < σ e) = S := by
          have hσe_val : σ e = ⟨k, hk⟩ := by simp [σ, heS, heT]
          ext f
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, hσe_val]
          by_cases hfS : f ∈ S
          · have h1 : (eL ⟨f, hfS⟩).1 ∈ L := (eL ⟨f, hfS⟩).2
            simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at h1
            simp [σ, hfS, h1]
          · by_cases hfT : f ∈ T
            · have h1 : (eR ⟨f, hfT⟩).1 ∈ R := (eR ⟨f, hfT⟩).2
              simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at h1
              simp only [σ, Equiv.coe_fn_mk, hfS, ↓reduceDIte, hfT, iff_false, not_lt]
              omega
            · simp [σ, hfS, hfT]
        ⟨σ, hσ_eq⟩
      left_inv := fun ⟨σ, hσ⟩ => by
        apply Subtype.ext
        ext f
        have h_e : σ e = ⟨k, hk⟩ := hσe σ hσ
        by_cases hfS : f ∈ S
        · simp [hfS]
        · by_cases hfT : f ∈ T
          · simp [hfS, hfT]
          · have hfe : f = e := by
              by_contra hne
              exact hfT (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_univ f⟩, hfS⟩)
            subst hfe
            simp [heS, heT, h_e]
      right_inv := fun ⟨eL, eR⟩ => by
        refine Prod.ext ?_ ?_
        · ext f
          simp
        · ext f
          have hnotS : f.1 ∉ S := (Finset.mem_sdiff.mp f.2).2
          simp [hnotS] }
  rw [← Fintype.card_subtype, Fintype.card_congr equivSplit, Fintype.card_prod]
  rw [card_equiv_of_card_eq (by rw [Fintype.card_coe, Fintype.card_coe, hL_card]),
    card_equiv_of_card_eq (by rw [Fintype.card_coe, Fintype.card_coe, hR_card]),
    Fintype.card_coe, Fintype.card_coe]

end Helpers

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ) (e : E) (u v : V) (huv : G.ends e = s(u, v)) :
    prob p y (attProb aT p y) (fun σ Y A P =>
        SideOK G t e u (arrivedBefore σ e) Y A P ∧ SideOK G t e v (arrivedBefore σ e) Y A P) =
      ∫ x in (0 : ℝ)..1, sideProb G p t y aT e u x * sideProb G p t y aT e v x := by
  classical
  let F : (E → Bool) → ℝ := fun B =>
    ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
      coinWeight y Y * coinWeight (attProb aT p y) A * coinWeight p P *
        (if SideOK G t e u B Y A P ∧ SideOK G t e v B Y A P then 1 else 0)
  have hF_indep : ∀ B₁ B₂, (∀ f ≠ e, B₁ f = B₂ f) → F B₁ = F B₂ := by
    intro B₁ B₂ hB
    refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun A _ =>
      Finset.sum_congr rfl fun P _ => ?_
    have hu : SideOK G t e u B₁ Y A P ↔ SideOK G t e u B₂ Y A P :=
      sideOK_congr G t e u (fun f hf =>
        ⟨hB f (Finset.mem_erase.mp hf).1, rfl, rfl, rfl⟩)
    have hv : SideOK G t e v B₁ Y A P ↔ SideOK G t e v B₂ Y A P :=
      sideOK_congr G t e v (fun f hf =>
        ⟨hB f (Finset.mem_erase.mp hf).1, rfl, rfl, rfl⟩)
    simp [hu, hv]
  have hRHS :
      ∫ x in (0 : ℝ)..1, sideProb G p t y aT e u x * sideProb G p t y aT e v x =
        ∑ S ∈ (Finset.univ.erase e).powerset,
          (((S.card.factorial : ℝ) * (((Finset.univ.erase e) \ S).card.factorial : ℝ)) /
            ((Fintype.card E).factorial : ℝ)) * F (fun f => decide (f ∈ S)) := by
    have hintegrand : ∀ x : ℝ,
        sideProb G p t y aT e u x * sideProb G p t y aT e v x =
          ∑ S ∈ (Finset.univ.erase e).powerset,
            x ^ S.card * (1 - x) ^ ((Finset.univ.erase e) \ S).card *
              F (fun f => decide (f ∈ S)) := by
      intro x
      rw [sideProb_mul_sideProb G hG p y t aT e u v huv x]
      exact sum_coinWeight_const_mul e F hF_indep x
    simp_rw [hintegrand]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun S hS => ?_
      rw [intervalIntegral.integral_mul_const, integral_pow_mul_one_sub_pow]
      have hsub : S ⊆ Finset.univ.erase e := Finset.mem_powerset.mp hS
      have hcard : S.card + ((Finset.univ.erase e) \ S).card + 1 = Fintype.card E := by
        have h1 : ((Finset.univ.erase e) \ S).card + S.card = (Finset.univ.erase e).card :=
          Finset.card_sdiff_add_card_eq_card hsub
        have h2 : (Finset.univ.erase e).card + 1 = Fintype.card E := by
          rw [Finset.card_erase_add_one (Finset.mem_univ e), Finset.card_univ]
        omega
      rw [hcard]
    · intro S _
      exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have hLHS :
      prob p y (attProb aT p y) (fun σ Y A P =>
          SideOK G t e u (arrivedBefore σ e) Y A P ∧ SideOK G t e v (arrivedBefore σ e) Y A P) =
        ∑ S ∈ (Finset.univ.erase e).powerset,
          (((S.card.factorial : ℝ) * (((Finset.univ.erase e) \ S).card.factorial : ℝ)) /
            ((Fintype.card E).factorial : ℝ)) * F (fun f => decide (f ∈ S)) := by
    have hprob_eq :
        prob p y (attProb aT p y) (fun σ Y A P =>
            SideOK G t e u (arrivedBefore σ e) Y A P ∧ SideOK G t e v (arrivedBefore σ e) Y A P) =
          (1 / ((Fintype.card E).factorial : ℝ)) *
            ∑ σ : E ≃ Fin (Fintype.card E), F (arrivedBefore σ e) := by
      unfold prob
      congr 1
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun Y _ =>
        Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun P _ => ?_
      congr 1
      by_cases h : SideOK G t e u (arrivedBefore σ e) Y A P ∧
          SideOK G t e v (arrivedBefore σ e) Y A P <;> simp [h]
    rw [hprob_eq]
    have hmaps : ∀ σ ∈ (Finset.univ : Finset (E ≃ Fin (Fintype.card E))),
        Finset.univ.filter (fun f => σ f < σ e) ∈ (Finset.univ.erase e).powerset := by
      intro σ _
      rw [Finset.mem_powerset]
      intro f hf
      rw [Finset.mem_filter] at hf
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ f⟩
      intro hfe
      subst hfe
      exact lt_irrefl _ hf.2
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hsub : S ⊆ Finset.univ.erase e := Finset.mem_powerset.mp hS
    have hinner :
        ∑ σ ∈ Finset.univ.filter (fun σ : E ≃ Fin (Fintype.card E) =>
            Finset.univ.filter (fun f => σ f < σ e) = S),
          F (arrivedBefore σ e) =
        ((S.card.factorial : ℝ) * (((Finset.univ.erase e) \ S).card.factorial : ℝ)) *
          F (fun f => decide (f ∈ S)) := by
      have hcongr :
          ∑ σ ∈ Finset.univ.filter (fun σ : E ≃ Fin (Fintype.card E) =>
              Finset.univ.filter (fun f => σ f < σ e) = S),
            F (arrivedBefore σ e) =
          ∑ _σ ∈ Finset.univ.filter (fun σ : E ≃ Fin (Fintype.card E) =>
              Finset.univ.filter (fun f => σ f < σ e) = S),
            F (fun f => decide (f ∈ S)) := by
        refine Finset.sum_congr rfl fun σ hσ => ?_
        rw [Finset.mem_filter] at hσ
        congr 1
        funext f
        rw [← hσ.2]
        simp [arrivedBefore]
      rw [hcongr, Finset.sum_const, nsmul_eq_mul, card_perm_beforeSet e S hsub]
      push_cast
      rfl
    rw [hinner]
    ring
  rw [hLHS, hRHS]

-- Prove2me | solution 1 for Schwichtenberg1976.normal_subterm_structure
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:51:00.024963+00:00
-- url     : https://prove2.me/submissions/d7091b52-9c8c-490e-a43c-d81553e733cb

import Definitions.Def_Schwichtenberg1976_Lambda

namespace Schwichtenberg1976.NSSAux
open Schwichtenberg1976

theorem ty_unique : ∀ {t : Term} {τ τ' : Ty}, HasType t τ → HasType t τ' → τ = τ'
  | _, _, _, .var _, .var _ => rfl
  | _, _, _, .app h1 h2, .app h1' h2' => by
      have := ty_unique h1 h1'; injection this
  | _, _, _, .lam _ h, .lam _ h' => by rw [ty_unique h h']

theorem lam_inv {x : Var} {b : Term} {τ : Ty} (h : HasType (.lam x b) τ) :
    ∃ τb, HasType b τb ∧ τ = .arr x.ty τb := by
  cases h with
  | lam _ hb => exact ⟨_, hb, rfl⟩

def Good (Fs : List Var) (α : Var) (t : Term) : Prop :=
  ∀ v ∈ freeVarOccurrences t, v ∈ Fs ∨ v = α ∨ v.ty = .zero

def AllSub (Fs : List Var) (α : Var) (t : Term) : Prop :=
  ∀ s τ, IsSubterm s t → HasType s τ →
    (τ = .zero ∨ τ = Ty.endo ∨ τ = Ty.nu) ∧
    (τ = Ty.nu → ∃ F ∈ Fs, s = .var F) ∧
    (τ = Ty.endo → IsType00Subterm Fs α s)

theorem endo_ne_zero : Ty.endo ≠ Ty.zero := by simp [Ty.endo]
theorem nu_ne_zero : Ty.nu ≠ Ty.zero := by simp [Ty.nu]
theorem nu_ne_endo : Ty.nu ≠ Ty.endo := by simp [Ty.nu, Ty.endo]

/-- Lemma H: non-λ normal good terms have type ν, 0→0 or 0, and type ν only for `F ∈ Fs`. -/
theorem headType (Fs : List Var) (α : Var) (hFs : ∀ F ∈ Fs, F.ty = Ty.nu)
    (hα : α.ty = Ty.endo) : ∀ (t : Term) (τ : Ty), (∀ x b, t ≠ .lam x b) →
    hasBetaRedex t = false → Good Fs α t → HasType t τ →
    (τ = .zero ∨ τ = Ty.endo ∨ τ = Ty.nu) ∧ (τ = Ty.nu → ∃ F ∈ Fs, t = .var F)
  | .var v, τ, _, _, hg, ht => by
      cases ht
      rcases hg v (by simp [freeVarOccurrences]) with h | h | h
      · exact ⟨Or.inr (Or.inr (hFs v h)), fun _ => ⟨v, h, rfl⟩⟩
      · subst h; refine ⟨Or.inr (Or.inl hα), fun h' => ?_⟩
        rw [hα] at h'; exact absurd h'.symm nu_ne_endo
      · refine ⟨Or.inl h, fun h' => ?_⟩
        rw [h] at h'; exact absurd h'.symm nu_ne_zero
  | .lam x b, _, hl, _, _, _ => absurd rfl (hl x b)
  | .app f a, τ, _, hn, hg, ht => by
      cases ht with
      | app hf ha =>
        rename_i σ
        have hfl : ∀ x b, f ≠ .lam x b := by
          rintro x b rfl; simp [hasBetaRedex] at hn
        have hnf : hasBetaRedex f = false := by
          cases f with
          | lam x b => exact absurd rfl (hfl x b)
          | var _ => simp [hasBetaRedex] at hn ⊢
          | app _ _ => simp [hasBetaRedex] at hn ⊢; exact hn.1
        have hgf : Good Fs α f := fun v hv => hg v (by simp [freeVarOccurrences, hv])
        obtain ⟨h1, _⟩ := headType Fs α hFs hα f _ hfl hnf hgf hf
        rcases h1 with h | h | h
        · cases h
        · simp only [Ty.endo, Ty.arr.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ⟨Or.inl rfl, fun h' => absurd h'.symm nu_ne_zero⟩
        · simp only [Ty.nu, Ty.arr.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ⟨Or.inr (Or.inl rfl), fun h' => absurd h'.symm nu_ne_endo⟩

theorem chain_zero {Fs : List Var} {α z : Var} : {t : Term} →
    IsBasicType00Chain Fs α z t → z.ty = .zero
  | _, .base _ hz => hz
  | _, .step _ h => chain_zero h

theorem basic_of_sub {Fs : List Var} {α : Var} {t : Term}
    (h : IsType00Subterm Fs α t) (hl : ∀ x b, t ≠ .lam x b) : IsBasicType00 Fs α t := by
  cases h with
  | basic h => exact h
  | chainLam y z _ _ _ => exact absurd rfl (hl _ _)

theorem main (Fs : List Var) (α : Var) (hFs : ∀ F ∈ Fs, F.ty = Ty.nu)
    (hα : α.ty = Ty.endo) : ∀ t : Term, hasBetaRedex t = false → Good Fs α t →
    (HasType t Ty.endo → IsType00Subterm Fs α t ∧ AllSub Fs α t) ∧
    (HasType t .zero → (∃ z, IsBasicType00Chain Fs α z t) ∧ AllSub Fs α t) ∧
    (HasType t Ty.nu → (∀ x b, t ≠ .lam x b) → AllSub Fs α t)
  | .var v, _, hg => by
      have self : ∀ τ0, HasType (.var v) τ0 → ((τ0 = .zero ∨ τ0 = Ty.endo ∨ τ0 = Ty.nu) ∧
          (τ0 = Ty.nu → ∃ F ∈ Fs, Term.var v = .var F) ∧
          (τ0 = Ty.endo → IsType00Subterm Fs α (.var v))) → AllSub Fs α (.var v) := by
        intro τ0 h0 hc s τ hs hτ
        cases hs
        rw [ty_unique hτ h0]; exact hc
      have hv : HasType (.var v) v.ty := HasType.var v
      rcases hg v (by simp [freeVarOccurrences]) with h | h | h
      · have hty := hFs v h
        refine ⟨fun he => ?_, fun hz => ?_, fun _ _ => self _ hv ⟨Or.inr (Or.inr hty),
          fun _ => ⟨v, h, rfl⟩, fun h' => absurd (hty.symm.trans h') nu_ne_endo⟩⟩
        · exact absurd ((ty_unique hv he).symm.trans hty).symm nu_ne_endo
        · exact absurd ((ty_unique hv hz).symm.trans hty).symm nu_ne_zero
      · subst h
        have ib : IsType00Subterm Fs v (.var v) := .basic .alpha
        have all := self _ hv ⟨Or.inr (Or.inl hα), fun h' => absurd (h'.symm.trans hα) nu_ne_endo,
          fun _ => ib⟩
        refine ⟨fun _ => ⟨ib, all⟩, fun hz => ?_, fun _ _ => all⟩
        exact absurd ((ty_unique hv hz).symm.trans hα).symm endo_ne_zero
      · have all := self _ hv ⟨Or.inl h, fun h' => absurd (h.symm.trans h') nu_ne_zero.symm,
          fun h' => absurd (h.symm.trans h') endo_ne_zero.symm⟩
        refine ⟨fun he => ?_, fun _ => ⟨⟨v, .base v h⟩, all⟩, fun _ _ => all⟩
        exact absurd ((ty_unique hv he).symm.trans h) endo_ne_zero
  | .lam x b, hn, hg => by
      have hnb : hasBetaRedex b = false := by simpa [hasBetaRedex] using hn
      refine ⟨fun he => ?_, fun hz => ?_, fun _ hl => absurd rfl (hl x b)⟩
      · obtain ⟨τb, hb, hτe⟩ := lam_inv he
        have hτe' : Ty.arr .zero .zero = .arr x.ty τb := hτe
        simp only [Ty.arr.injEq] at hτe'
        obtain ⟨hx0, rfl⟩ := hτe'
        have hxty : x.ty = .zero := hx0.symm
        have hgb : Good Fs α b := by
          intro v hv
          by_cases hvx : v = x
          · subst hvx; exact Or.inr (Or.inr hxty)
          · exact hg v (by simp [freeVarOccurrences, List.mem_filter, hv, hvx])
        obtain ⟨⟨z, hc⟩, allb⟩ := (main Fs α hFs hα b hnb hgb).2.1 hb
        have ib : IsType00Subterm Fs α (.lam x b) := .chainLam x z hxty (chain_zero hc) hc
        refine ⟨ib, ?_⟩
        intro s τ hs hτ
        cases hs with
        | refl =>
          rw [ty_unique hτ he]
          exact ⟨Or.inr (Or.inl rfl), fun h' => absurd h' nu_ne_endo.symm, fun _ => ib⟩
        | lamBody _ hs' => exact allb s τ hs' hτ
      · cases hz
  | .app f a, hn, hg => by
      have hfl : ∀ x b, f ≠ .lam x b := by
        rintro x b rfl; simp [hasBetaRedex] at hn
      have hnf : hasBetaRedex f = false ∧ hasBetaRedex a = false := by
        cases f with
        | lam x b => exact absurd rfl (hfl x b)
        | var _ => simp [hasBetaRedex] at hn ⊢; exact hn
        | app _ _ => simp [hasBetaRedex] at hn ⊢; exact hn
      have hgf : Good Fs α f := fun v hv => hg v (by simp [freeVarOccurrences, hv])
      have hga : Good Fs α a := fun v hv => hg v (by simp [freeVarOccurrences, hv])
      have IHf := main Fs α hFs hα f hnf.1 hgf
      have IHa := main Fs α hFs hα a hnf.2 hga
      have mkAll : AllSub Fs α f → AllSub Fs α a → (∀ τ, HasType (.app f a) τ →
          (τ = .zero ∨ τ = Ty.endo ∨ τ = Ty.nu) ∧ (τ = Ty.nu → ∃ F ∈ Fs, Term.app f a = .var F) ∧
          (τ = Ty.endo → IsType00Subterm Fs α (.app f a))) → AllSub Fs α (.app f a) := by
        intro af aa hself s τ hs hτ
        cases hs with
        | refl => exact hself τ hτ
        | appLeft hs' => exact af s τ hs' hτ
        | appRight hs' => exact aa s τ hs' hτ
      refine ⟨fun he => ?_, fun hz => ?_, fun hnu _ => ?_⟩
      · cases he with
        | app hf ha =>
          rename_i σ
          obtain ⟨h1, h2⟩ := headType Fs α hFs hα f _ hfl hnf.1 hgf hf
          rcases h1 with h | h | h
          · cases h
          · simp [Ty.endo] at h
          · simp only [Ty.nu, Ty.arr.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨F, hF, rfl⟩ := h2 (by simp [Ty.nu])
            obtain ⟨ia, aa⟩ := IHa.1 ha
            have ib : IsType00Subterm Fs α (.app (.var F) a) := .basic (.appF hF ia)
            refine ⟨ib, mkAll (IHf.2.2 hf (fun x b h => by cases h)) aa (fun τ hτ => ?_)⟩
            rw [ty_unique hτ (HasType.app hf ha)]
            exact ⟨Or.inr (Or.inl rfl), fun h' => absurd h' nu_ne_endo.symm, fun _ => ib⟩
      · cases hz with
        | app hf ha =>
          rename_i σ
          obtain ⟨h1, -⟩ := headType Fs α hFs hα f _ hfl hnf.1 hgf hf
          rcases h1 with h | h | h
          · cases h
          · simp only [Ty.endo, Ty.arr.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨if', af⟩ := IHf.1 hf
            obtain ⟨⟨z, hc⟩, aa⟩ := IHa.2.1 ha
            refine ⟨⟨z, .step (basic_of_sub if' hfl) hc⟩, mkAll af aa (fun τ hτ => ?_)⟩
            rw [ty_unique hτ (HasType.app hf ha)]
            exact ⟨Or.inl rfl, fun h' => absurd h'.symm nu_ne_zero,
              fun h' => absurd h'.symm endo_ne_zero⟩
          · simp [Ty.nu, Ty.endo] at h
      · cases hnu with
        | app hf ha =>
          obtain ⟨h1, -⟩ := headType Fs α hFs hα f _ hfl hnf.1 hgf hf
          rcases h1 with h | h | h
          · cases h
          · simp [Ty.endo, Ty.nu] at h
          · simp [Ty.nu, Ty.endo] at h

end Schwichtenberg1976.NSSAux

open Schwichtenberg1976 Schwichtenberg1976.NSSAux in
theorem solution
    (Fs : List Var) (α : Var) (r : Term)
    (hFs : ∀ F ∈ Fs, F.ty = Ty.nu)
    (hα : α.ty = Ty.endo)
    (hr_ty : HasType r Ty.endo)
    (hr_norm : IsBetaNormal r)
    (hr_fv : ∀ v ∈ freeVars r, v ∈ Fs ∨ v = α) :
    (∀ s τ, IsSubterm s r → HasType s τ → τ = .zero ∨ τ = Ty.endo ∨ τ = Ty.nu) ∧
    (∀ s, IsSubterm s r → HasType s Ty.nu → ∃ F ∈ Fs, s = .var F) ∧
    (∀ s, IsSubterm s r → HasType s Ty.endo → IsType00Subterm Fs α s) := by
  have hg : Good Fs α r := by
    intro v hv
    have : v ∈ freeVars r := by unfold freeVars; exact List.mem_eraseDups.2 hv
    rcases hr_fv v this with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨-, all⟩ := (main Fs α hFs hα r hr_norm hg).1 hr_ty
  exact ⟨fun s τ hs hτ => (all s τ hs hτ).1, fun s hs hτ => (all s _ hs hτ).2.1 rfl,
    fun s hs hτ => (all s _ hs hτ).2.2 rfl⟩

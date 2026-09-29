-- Prove2me | solution 1 for PathCover.homotopic_concat_insert
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-10T09:46:47.920925+00:00
-- url     : https://prove2.me/submissions/669983a6-a178-4ad7-814c-21cb2c860116

import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Tactic

open scoped unitInterval
open Set


local notation "⟪" p "⟫" => Path.Homotopic.Quotient.mk p

private lemma algebra {X : Type*} [TopologicalSpace X] {a b c d : X}
    (A : Path.Homotopic.Quotient a b) (C : Path.Homotopic.Quotient b c)
    (q : Path.Homotopic.Quotient a c) (F : Path.Homotopic.Quotient c d)
    (r : Path.Homotopic.Quotient a d) :
    (A.trans (C.trans q.symm)).trans (q.trans (F.trans r.symm))
      = A.trans ((C.trans F).trans r.symm) := by
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc q.symm q, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

private lemma aux {X : Type*} [TopologicalSpace X] (x0 : X) : ∀ {n : ℕ}
    (p : Fin (n + 1) → X)
    (f : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (g : (k : Fin (n + 1)) → Path x0 (p k)),
    ⟪Path.concat (fun _ : Fin (n + 1) => x0)
        (fun k => (g k.castSucc).trans ((f k).trans (g k.succ).symm))⟫
      = (⟪g 0⟫).trans ((⟪Path.concat p f⟫).trans (⟪g (Fin.last n)⟫).symm) := by
  intro n
  induction n with
  | zero =>
    intro p f g
    rw [Path.concat_zero, Path.concat_zero]
    simp
  | succ n ih =>
    intro p f g
    have hR : ⟪Path.concat p f⟫
        = (⟪Path.concat (p ∘ Fin.castSucc) (fun k => f k.castSucc)⟫).trans ⟪f (Fin.last n)⟫ := by
      rw [Path.concat_succ]
      rfl
    have hL : ⟪Path.concat (fun _ : Fin (n + 2) => x0)
          (fun k => (g k.castSucc).trans ((f k).trans (g k.succ).symm))⟫
        = (⟪Path.concat (fun _ : Fin (n + 1) => x0)
            (fun k : Fin n => (g k.castSucc.castSucc).trans
              ((f k.castSucc).trans (g k.succ.castSucc).symm))⟫).trans
          ((⟪g (Fin.last n).castSucc⟫).trans
            ((⟪f (Fin.last n)⟫).trans (⟪g (Fin.last n).succ⟫).symm)) := by
      rw [Path.concat_succ]
      rfl
    have hIH := ih (p ∘ Fin.castSucc) (fun k => f k.castSucc) (fun k => g k.castSucc)
    rw [hL, hR, hIH]
    exact algebra _ _ _ _ _

private lemma cast_eq_conj {X : Type*} [TopologicalSpace X] {a b x0 : X}
    (γ : Path.Homotopic.Quotient a b) (h0 : a = x0) (hn : b = x0) :
    γ.cast h0.symm hn.symm
      = (⟪(Path.refl x0).cast rfl h0⟫).trans (γ.trans (⟪(Path.refl x0).cast rfl hn⟫).symm) := by
  subst h0; subst hn
  simp [show ∀ y : X, (Path.Homotopic.Quotient.refl y).symm = Path.Homotopic.Quotient.refl y from
    fun _ => rfl]

/-- Inserting return paths at the subdivision points.  Given a chain of paths `f k` through
points `p k`, and paths `g k` from a basepoint `x₀` to each `p k` with the two outer ones
constant, the concatenation of the `f k` is homotopic rel endpoints to the concatenation of the
loops `g k · f k · (g (k+1))⁻¹`. -/
theorem homotopic_concat_insert {X : Type*} [TopologicalSpace X] (x0 : X) {n : ℕ}
    (p : Fin (n + 1) → X)
    (f : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (g : (k : Fin (n + 1)) → Path x0 (p k))
    (h0 : p 0 = x0) (hn : p (Fin.last n) = x0)
    (hg0 : g 0 = (Path.refl x0).cast rfl h0)
    (hgn : g (Fin.last n) = (Path.refl x0).cast rfl hn) :
    ((Path.concat p f).cast h0.symm hn.symm).Homotopic
      (Path.concat (fun _ : Fin (n + 1) => x0)
        (fun k => (g k.castSucc).trans ((f k).trans (g k.succ).symm))) := by
  refine Path.Homotopic.Quotient.eq.mp ?_
  rw [aux x0 p f g, hg0, hgn]
  exact cast_eq_conj ⟪Path.concat p f⟫ h0 hn

/-! ### The nullhomotopic variant -/

/-- If a path `γ` from `x₀` to `a`, read as a loop at `x₀` via `h : a = x₀`, is nullhomotopic,
then its class in the fundamental groupoid is the class of the pinned constant path. -/
private lemma mk_eq_of_nullhomotopic {X : Type*} [TopologicalSpace X] {x0 a : X} (h : a = x0)
    (γ : Path x0 a) (hγ : (γ.cast rfl h.symm).Homotopic (Path.refl x0)) :
    ⟪γ⟫ = ⟪(Path.refl x0).cast rfl h⟫ := by
  subst h
  -- `Path.cast _ rfl rfl = _` is definitional, so both casts disappear.
  exact Path.Homotopic.Quotient.eq.mpr hγ

/-- The nullhomotopic-hypothesis variant of `PathCover.homotopic_concat_insert`: it suffices
that the two outer paths `g 0` and `g (Fin.last n)`, read as loops at `x₀` via `h0`/`hn`, are
nullhomotopic (rather than literally being the constant path). -/

theorem solution {X : Type*} [TopologicalSpace X] (x0 : X) {n : ℕ}
    (p : Fin (n + 1) → X)
    (f : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (g : (k : Fin (n + 1)) → Path x0 (p k))
    (h0 : p 0 = x0) (hn : p (Fin.last n) = x0)
    (hg0 : ((g 0).cast rfl h0.symm).Homotopic (Path.refl x0))
    (hgn : ((g (Fin.last n)).cast rfl hn.symm).Homotopic (Path.refl x0)) :
    ((Path.concat p f).cast h0.symm hn.symm).Homotopic
      (Path.concat (fun _ : Fin (n + 1) => x0)
        (fun k => (g k.castSucc).trans ((f k).trans (g k.succ).symm))) := by
  refine Path.Homotopic.Quotient.eq.mp ?_
  rw [aux x0 p f g, mk_eq_of_nullhomotopic h0 (g 0) hg0,
    mk_eq_of_nullhomotopic hn (g (Fin.last n)) hgn]
  exact cast_eq_conj ⟪Path.concat p f⟫ h0 hn

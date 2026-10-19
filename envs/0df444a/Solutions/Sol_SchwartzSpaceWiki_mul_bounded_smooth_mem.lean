-- Prove2me | solution 1 for SchwartzSpaceWiki.mul_bounded_smooth_mem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:33:16.939485+00:00
-- url     : https://prove2.me/submissions/b2a7154f-3208-485c-abc4-06e5950aee7b

import Definitions.Def_SchwartzSpaceWiki_Defs

open SchwartzSpaceWiki
open scoped ENNReal

private lemma partial_smooth {n : ℕ} (i : Fin n) {f : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (partialDeriv i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private lemma partial_add {n : ℕ} (i : Fin n) {f g : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    partialDeriv i (f + g) = partialDeriv i f + partialDeriv i g := by
  ext x
  simp [partialDeriv, fderiv_add ((hf.differentiable (by simp)) x)
    ((hg.differentiable (by simp)) x)]

private lemma partial_mul {n : ℕ} (i : Fin n) {f g : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    partialDeriv i (f * g) = partialDeriv i f * g + f * partialDeriv i g := by
  ext x
  simp [partialDeriv, fderiv_mul ((hf.differentiable (by simp)) x)
    ((hg.differentiable (by simp)) x), mul_comm, add_comm]

private inductive SumProd {n : ℕ} (P Q : (Rn n → ℂ) → Prop) : (Rn n → ℂ) → Prop
  | mul {f g} : P f → Q g → SumProd P Q (f * g)
  | add {f g} : SumProd P Q f → SumProd P Q g → SumProd P Q (f + g)

private lemma sumProd_map {n : ℕ} {P Q P' Q' : (Rn n → ℂ) → Prop}
    (hP : ∀ f, P f → P' f) (hQ : ∀ g, Q g → Q' g)
    {h} (hh : SumProd P Q h) : SumProd P' Q' h := by
  induction hh with
  | mul hf hg => exact SumProd.mul (hP _ hf) (hQ _ hg)
  | add _ _ ih ih' => exact ih.add ih'

private lemma sumProd_smooth {n : ℕ} {P Q : (Rn n → ℂ) → Prop}
    (hP : ∀ f, P f → ContDiff ℝ (⊤ : ℕ∞) f)
    (hQ : ∀ g, Q g → ContDiff ℝ (⊤ : ℕ∞) g)
    {h} (hh : SumProd P Q h) : ContDiff ℝ (⊤ : ℕ∞) h := by
  induction hh with
  | mul hf hg => exact (hP _ hf).mul (hQ _ hg)
  | add _ _ ih ih' => exact ih.add ih'

private lemma sumProd_partial {n : ℕ} {P Q : (Rn n → ℂ) → Prop}
    (hP : ∀ f, P f → ContDiff ℝ (⊤ : ℕ∞) f)
    (hQ : ∀ g, Q g → ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin n) (dP : ∀ f, P f → P (partialDeriv i f))
    (dQ : ∀ g, Q g → Q (partialDeriv i g))
    {h} (hh : SumProd P Q h) : SumProd P Q (partialDeriv i h) := by
  induction hh with
  | mul hf hg =>
    rw [partial_mul i (hP _ hf) (hQ _ hg)]
    exact (SumProd.mul (dP _ hf) hg).add (SumProd.mul hf (dQ _ hg))
  | add hf hg ih ih' =>
    rw [partial_add i (sumProd_smooth hP hQ hf) (sumProd_smooth hP hQ hg)]
    exact ih.add ih'

private noncomputable def D {n : ℕ} (l : List (Fin n)) (β : MultiIndex n)
    (f : Rn n → ℂ) : Rn n → ℂ :=
  l.foldr (fun i h => (partialDeriv i)^[β i] h) f

private lemma iterate_smooth {n : ℕ} (i : Fin n) (k : ℕ) {f : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => simpa only [Function.iterate_succ_apply'] using partial_smooth i ih

private lemma D_smooth {n : ℕ} (l : List (Fin n)) (β : MultiIndex n) {f : Rn n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (D l β f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact iterate_smooth i (β i) ih

private lemma D_congr {n : ℕ} (l : List (Fin n)) (β γ : MultiIndex n)
    (h : ∀ i ∈ l, β i = γ i) (f : Rn n → ℂ) : D l β f = D l γ f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (partialDeriv i)^[β i] (D l β f) = (partialDeriv i)^[γ i] (D l γ f)
    rw [h i (by simp), show D l β f = D l γ f from ih (fun j hj => h j (by simp [hj]))]

private lemma D_prefix {n : ℕ} (i : Fin n) (l : List (Fin n)) (hi : i ∉ l)
    (k : ℕ) (β : MultiIndex n) (f : Rn n → ℂ) :
    (partialDeriv i)^[k] (D l β f) = D (i :: l) (Function.update β i k) f := by
  classical
  change _ = (partialDeriv i)^[Function.update β i k i] (D l (Function.update β i k) f)
  rw [Function.update_self]
  congr 1
  apply D_congr
  intro j hj
  exact (Function.update_of_ne (show j ≠ i from fun e => hi (e ▸ hj)) k β).symm

private lemma D_leibniz {n : ℕ} (l : List (Fin n)) (hl : l.Nodup) (β : MultiIndex n)
    (f g : Rn n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    SumProd (fun h => ∃ γ, h = D l γ f) (fun h => ∃ δ, h = D l δ g) (D l β (f * g)) := by
  induction l with
  | nil => exact SumProd.mul ⟨0, rfl⟩ ⟨0, rfl⟩
  | cons i l ih =>
    have hi := (List.nodup_cons.mp hl).1
    let P := fun (u h : Rn n → ℂ) => ∃ k γ, h = (partialDeriv i)^[k] (D l γ u)
    have hs (u : Rn n → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
        ∀ h, P u h → ContDiff ℝ (⊤ : ℕ∞) h := by
      rintro h ⟨k, γ, rfl⟩
      exact iterate_smooth i k (D_smooth l γ hu)
    have hd (u : Rn n → ℂ) : ∀ h, P u h → P u (partialDeriv i h) := by
      rintro h ⟨k, γ, rfl⟩
      exact ⟨k + 1, γ, (Function.iterate_succ_apply' _ _ _).symm⟩
    have ht : SumProd (P f) (P g) (D l β (f * g)) :=
      sumProd_map (fun _ ⟨γ, he⟩ => ⟨0, γ, he⟩)
        (fun _ ⟨δ, he⟩ => ⟨0, δ, he⟩) (ih (List.nodup_cons.mp hl).2)
    have hk : ∀ k, SumProd (P f) (P g) ((partialDeriv i)^[k] (D l β (f * g))) := by
      intro k
      induction k with
      | zero => exact ht
      | succ k ihk =>
        simpa only [Function.iterate_succ_apply'] using
          sumProd_partial (hs f hf) (hs g hg) i (hd f) (hd g) ihk
    apply sumProd_map (P := P f) (Q := P g) _ _ (hk (β i))
    · rintro h ⟨k, γ, rfl⟩
      exact ⟨Function.update γ i k, D_prefix i l hi k γ f⟩
    · rintro h ⟨k, δ, rfl⟩
      exact ⟨Function.update δ i k, D_prefix i l hi k δ g⟩

private lemma sumProd_bound {n : ℕ} {P Q : (Rn n → ℂ) → Prop} (w : Rn n → ℂ)
    (hP : ∀ f, P f → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, ‖w x * f x‖ₑ ≤ C)
    (hQ : ∀ g, Q g → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, ‖g x‖ₑ ≤ C)
    {h} (hh : SumProd P Q h) : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, ‖w x * h x‖ₑ ≤ C := by
  induction hh with
  | @mul f g hf hg =>
    obtain ⟨C, hC, hCf⟩ := hP _ hf
    obtain ⟨B, hB, hBg⟩ := hQ _ hg
    refine ⟨C * B, ENNReal.mul_lt_top hC hB, fun x => ?_⟩
    simpa only [Pi.mul_apply, ← mul_assoc, enorm_mul] using mul_le_mul' (hCf x) (hBg x)
  | @add f g hf hg ih ih' =>
    obtain ⟨C, hC, hCf⟩ := ih
    obtain ⟨B, hB, hBg⟩ := ih'
    exact ⟨C + B, ENNReal.add_lt_top.mpr ⟨hC, hB⟩, fun x => by
      simpa only [Pi.add_apply, mul_add] using
        (enorm_add_le _ _).trans (add_le_add (hCf x) (hBg x))⟩

theorem solution (n : ℕ) (f g : Rn n → ℂ) (hf : f ∈ schwartzSpace n)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hbdd : ∀ β : MultiIndex n, ∃ C : ℝ, ∀ x : Rn n, ‖iteratedPartialDeriv β g x‖ ≤ C) :
    f * g ∈ schwartzSpace n := by
  refine ⟨hf.1.mul hg, ?_⟩
  intro α β
  have ht := D_leibniz (List.finRange n) (List.nodup_finRange n) β f g hf.1 hg
  obtain ⟨C, hC, hCx⟩ := sumProd_bound (fun x => (monomial α x : ℂ))
    (fun u ⟨γ, he⟩ => by
      subst u
      exact ⟨schwartzSeminorm α γ f, hf.2 α γ, fun x => by
        change ‖(monomial α x : ℂ) * iteratedPartialDeriv γ f x‖ₑ ≤ _
        exact le_iSup (fun y => ‖(monomial α y : ℂ) * iteratedPartialDeriv γ f y‖ₑ) x⟩)
    (fun v ⟨δ, he⟩ => by
      subst v
      obtain ⟨B, hB⟩ := hbdd δ
      exact ⟨ENNReal.ofReal B, ENNReal.ofReal_lt_top, fun x => by
        simpa only [ofReal_norm, D, iteratedPartialDeriv] using ENNReal.ofReal_le_ofReal (hB x)⟩) ht
  exact (iSup_le hCx).trans_lt hC

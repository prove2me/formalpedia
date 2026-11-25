-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.adapted_semistable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:04:37.932822+00:00
-- url     : https://prove2.me/submissions/9bdf774d-e263-4d16-8352-83ccf12b769b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_cutSub_self
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_flag_base
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_flag_step
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_adMet_pos
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_exists_at
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gr_at
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_latDeg_single
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_mid_int
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_mid_le_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_mid_supp
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_pair_int
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_rankOne_le_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_sum_log_single
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_top_le_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution (hB : LatDegBasisStatement) (hN : IntegralIndexStatement)
    (hA : AbsDetStatement) (hE : GradedExtStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (S : HermForm K r) (m : ℕ) (g : Fin r → K) (h2m : 2 * m ≤ r)
    (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (hg0 : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0)
    (Lp : Submodule (𝓞 K) (Fin r → K)) (hLp : Lp.FG)
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp)
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    ∃ dd : Fin r → ℝ, (∀ i, 0 < dd i) ∧ ∀ B ≤ Lp, ∀ (k : ℕ) (b : Fin k → Fin r → K),
      IsKBasisIn B b → latDeg (diagMet (adMet r m g dd)) B b ≤ 0 := by
  classical
  choose x0 hx0 hx0j using exists_at Lp hsp
  have hn : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card (K →+* ℂ) : ℝ) with hn_def
  let Gr : Fin r → Submodule (𝓞 K) (Fin r → K) := fun j =>
    (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j)
  have hGrfg : ∀ j, (Gr j).FG := fun j => (Submodule.FG.of_le hLp inf_le_left).map _
  let dd : Fin r → ℝ := fun j => Real.exp ((2 / n) * (Real.log (spanIdx (Gr j) ![x0 j] : ℝ) -
    Real.log |((Algebra.norm ℚ (x0 j j) : ℚ) : ℝ)|))
  have hdd : ∀ j, 0 < dd j := fun j => Real.exp_pos _
  refine ⟨dd, hdd, ?_⟩
  set δ := adMet r m g dd with hδdef
  have hδ : ∀ σ a, 0 < δ σ a := adMet_pos r m g dd hdd hg0
  have hbot0 : ∀ j : Fin r, (j : ℕ) < m → latDeg (diagMet δ) (Gr j) ![x0 j] = 0 := by
    intro j hj
    rw [latDeg_single δ _ j (x0 j) (gr_at Lp j _ (hx0 j))]
    have hδj : ∀ σ, δ σ j = dd j := fun σ => by simp [hδdef, adMet, hj]
    simp only [hδj]
    rw [sum_log_single (x0 j j) (hx0j j) (dd j) (hdd j), Real.log_exp]
    field_simp
    ring

  have hGb : ∀ j : Fin r, (j : ℕ) < m → ∀ C ≤ Gr j, ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0 := fun j hj C hC k c hc =>
    rankOne_le_zero hB δ hδ j (Gr j) (hGrfg j) (gr_at Lp j) (x0 j) (hx0 j) (hx0j j)
      (hbot0 j hj).le C hC k c hc
  have hGt : ∀ p : Fin r, r ≤ (p : ℕ) + m → ∀ C ≤ Gr p, ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0 := by
    intro p hp C hC k c hc
    have hpr := p.isLt
    have hjv : ((Fin.rev p : Fin r) : ℕ) = r - (p + 1) := Fin.val_rev p
    have hj : ((Fin.rev p : Fin r) : ℕ) < m := by omega
    have hpj : Fin.rev (Fin.rev p) = p := Fin.rev_rev p
    have hjp : ((Fin.rev p : Fin r) : ℕ) < p := by omega
    have hpair := pair_int S m g h2m Lp hint (Fin.rev p) hj
    rw [hpj] at hpair
    have hδj : ∀ σ, δ σ (Fin.rev p) = dd (Fin.rev p) := fun σ => by
      show adMet r m g dd σ (Fin.rev p) = _
      unfold adMet
      rw [if_pos hj]
    have hδp : ∀ σ, δ σ p = (dd (Fin.rev p))⁻¹ := fun σ => by
      have h1 : ¬ (p : ℕ) < m := by omega
      simp [hδdef, adMet, h1, hp]
    have htop := top_le_zero hN S (Fin.rev p) p hjp (Gr (Fin.rev p)) (Gr p) (hGrfg _) (hGrfg p)
      (gr_at Lp _) (gr_at Lp p) hpair (x0 (Fin.rev p)) (x0 p) (hx0 _) (hx0j _) (hx0 p) (hx0j p)
      δ (dd (Fin.rev p)) (hdd _) hδj hδp (hbot0 _ hj)
    exact rankOne_le_zero hB δ hδ p (Gr p) (hGrfg p) (gr_at Lp p) (x0 p) (hx0 p) (hx0j p) htop
      C hC k c hc
  have hGm : ∀ C ≤ (Lp ⊓ cutSub K r (r - m)).map (projGe K r m), ∀ (k : ℕ)
      (c : Fin k → Fin r → K), IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0 := by
    intro C hC k c hc
    have hδmid : ∀ σ (a : Fin r), m ≤ (a : ℕ) → (a : ℕ) + m < r → δ σ a = ‖σ (g a)‖ := by
      intro σ a h1 h2
      have h1' : ¬ (a : ℕ) < m := by omega
      have h2' : ¬ r ≤ (a : ℕ) + m := by omega
      simp [hδdef, adMet, h1', h2']
    exact mid_le_zero hN hA S m g hfix _ ((Submodule.FG.of_le hLp inf_le_left).map _)
      (mid_supp m Lp) (mid_int S m g hfix Lp hint) haniso δ hδ hδmid C hC k c hc

  have P1 : ∀ e, e ≤ m → ∀ B ≤ Lp ⊓ cutSub K r e, ∀ (k : ℕ) (b : Fin k → Fin r → K),
      IsKBasisIn B b → latDeg (diagMet δ) B b ≤ 0 := by
    intro e
    induction e with
    | zero => intro _; exact flag_base _ Lp
    | succ e ih =>
      intro he
      exact flag_step hE δ hδ Lp hLp e (e + 1) (ih (by omega))
        (hGb ⟨e, by omega⟩ (by show e < m; omega))
  have P2 := flag_step hE δ hδ Lp hLp m (r - m) (P1 m le_rfl) hGm
  have P3 : ∀ t, t ≤ m → ∀ B ≤ Lp ⊓ cutSub K r (r - m + t), ∀ (k : ℕ)
      (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg (diagMet δ) B b ≤ 0 := by
    intro t
    induction t with
    | zero => intro _; simpa using P2
    | succ t ih =>
      intro ht
      exact flag_step hE δ hδ Lp hLp (r - m + t) (r - m + t + 1) (ih (by omega))
        (hGt ⟨r - m + t, by omega⟩ (by show r ≤ r - m + t + m; omega))
  intro B hB k b hb
  have hrm : r - m + m = r := by omega
  have := P3 m le_rfl
  rw [hrm, cutSub_self, inf_top_eq] at this
  exact this B hB k b hb
end ReciprocityTheory.MultiplicativeHeights.SemiPt

-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pairing_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:04:52.612294+00:00
-- url     : https://prove2.me/submissions/ff45164f-6a17-47ad-821b-b1be2365a855

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreFst_nsmul_mk
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreSnd_nsmul_mk
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_hcongr
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_zero1
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul2_hcongr
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul2_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution (N p : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) (hx : N • x = 0)
    (hy : (N * p) • y = 0) (h : B.IsPairing (N * p) x y z) : B.IsPairing N x (p • y) z := by
  obtain ⟨hx', hy', u, l₁, l₂, e₁, e₂, rfl⟩ := h
  have inj : ∀ {a b : B.G R} (v : B.P R a b) (l l' : (R : Type u)ˣ), B.smul l v = B.smul l' v → l = l' :=
    fun v l l' h => (B.trans v (B.smul l v)).unique rfl h.symm
  have hsmH : ∀ (c : (R : Type u)ˣ) {a a' b b' : B.G R} (ea : a = a') (eb : b = b') (v : B.P R a b)
      (v' : B.P R a' b'), HEq v v' → HEq (B.smul c v) (B.smul c v') := by
    intro c a a' b b' ea eb v v' hv
    subst ea
    subst eb
    rw [eq_of_heq hv]
  have htr1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a), HEq (B.tr1 e v) v := by
    intro a b b' e v
    subst e
    rfl
  have htr2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b), HEq (B.tr2 e v) v := by
    intro a b b' e v
    subst e
    rfl
  have hpy : N • (p • y) = 0 := by rw [smul_smul, hy]
  obtain ⟨c, hc, -⟩ := B.trans (B.zero1 y) (B.tr1 hx (B.nsmul1 u N))

  have hS1 : (⟨(N * p) • x, B.nsmul1 u (N * p)⟩ : B.S1 R y) = ⟨p • (N • x), B.nsmul1 (B.nsmul1 u N) p⟩ := by
    rw [← B.fibreFst_nsmul_mk, ← B.fibreFst_nsmul_mk,
      show B.S1mk (B.nsmul1 u N) = N • B.S1mk u from (B.fibreFst_nsmul_mk u N).symm, smul_smul, mul_comm]
  have hH1 : HEq (B.nsmul1 u (N * p)) (B.nsmul1 (B.nsmul1 u N) p) := (Sigma.mk.inj hS1).2
  have chain : HEq (B.smul l₁ (B.zero1 y)) (B.smul (c ^ p) (B.zero1 y)) := by
    refine (heq_of_eq e₁).symm.trans ((htr1 hx' _).trans (hH1.trans ?_))
    refine (B.nsmul1_hcongr hx rfl p ((htr1 hx _).symm.trans (heq_of_eq hc.symm))).trans ?_
    rw [B.nsmul1_smul]
    exact hsmH _ (smul_zero p) rfl _ _ (B.nsmul1_zero1 y p)
  have hl : l₁ = c ^ p := inj _ _ _ (eq_of_heq chain)

  have hS2 : (⟨N • (p • y), B.nsmul2 (B.nsmul2 u p) N⟩ : B.S2 R x) = ⟨(N * p) • y, B.nsmul2 u (N * p)⟩ := by
    rw [← B.fibreSnd_nsmul_mk, ← B.fibreSnd_nsmul_mk,
      show B.S2mk (B.nsmul2 u p) = p • B.S2mk u from (B.fibreSnd_nsmul_mk u p).symm, smul_smul]
  have hH2 : HEq (B.nsmul2 (B.nsmul2 u p) N) (B.nsmul2 u (N * p)) := (Sigma.mk.inj hS2).2
  refine ⟨hx, hpy, B.nsmul2 u p, c ^ p, l₂, ?_, ?_, by rw [hl]⟩
  · rw [← B.nsmul_comm]
    refine eq_of_heq ((htr1 hx _).trans ?_)
    refine (B.nsmul2_hcongr hx rfl p ((htr1 hx _).symm.trans (heq_of_eq hc.symm))).trans ?_
    rw [B.nsmul2_smul]
    exact hsmH _ rfl rfl _ _ (B.nsmul2_zero1 y p)
  · exact eq_of_heq ((htr2 hpy _).trans (hH2.trans ((htr2 hy' _).symm.trans (heq_of_eq e₂))))
end ReciprocityTheory.PGsh.BX

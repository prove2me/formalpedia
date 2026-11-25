-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pairing_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:01:49.466321+00:00
-- url     : https://prove2.me/submissions/3ea3d1e8-8e1e-4d05-9f64-9db80bc33957

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_hcongr
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_zero2
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
theorem _root_.solution (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) (h : B.IsPairing N x y z) :
    z ^ N = 1 := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
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

  have hz : B.zero1 (0 : B.G R) = B.zero2 0 := by
    obtain ⟨c, hc, -⟩ := B.trans (B.zero2 (0 : B.G R)) (B.zero1 0)
    have h1 : HEq (B.add1 (B.zero1 (0 : B.G R)) (B.zero2 0)) (B.zero2 (0 : B.G R)) := B.zeroFst_add _
    have h2 : B.add1 (B.zero1 (0 : B.G R)) (B.zero2 0) = B.smul c (B.zero2 (0 + 0 : B.G R)) := by
      rw [← hc, show B.add1 (B.smul c (B.zero2 (0 : B.G R))) (B.zero2 0) =
        B.add1 (B.smul c (B.zero2 (0 : B.G R))) (B.smul 1 (B.zero2 0)) by rw [B.one_smul],
        B.addFst_smul, mul_one, B.zeroSnd_addFst]
    have h3 : HEq (B.smul c (B.zero2 (0 + 0 : B.G R))) (B.smul c (B.zero2 (0 : B.G R))) :=
      hsmH c (add_zero 0) rfl _ _ (congr_arg_heq B.zero2 (add_zero (0 : B.G R)))
    have h4 : HEq (B.smul c (B.zero2 (0 : B.G R))) (B.zero2 (0 : B.G R)) := h3.symm.trans (h2 ▸ h1)
    have hc1 : c = 1 := inj _ _ _ ((eq_of_heq h4).trans (B.one_smul _).symm)
    rw [← hc, hc1, B.one_smul]

  have L : HEq (B.nsmul2 (B.nsmul1 u N) N) (B.smul (l₁ ^ N) (B.zero1 (0 : B.G R))) := by
    have a1 : HEq (B.nsmul1 u N) (B.smul l₁ (B.zero1 y)) := (htr1 hx _).symm.trans (heq_of_eq e₁)
    refine (B.nsmul2_hcongr hx rfl N a1).trans ?_
    rw [B.nsmul2_smul]
    exact hsmH _ rfl hy _ _ ((B.nsmul2_zero1 y N).trans (congr_arg_heq B.zero1 hy))
  have Rr : HEq (B.nsmul1 (B.nsmul2 u N) N) (B.smul (l₂ ^ N) (B.zero2 (0 : B.G R))) := by
    have a2 : HEq (B.nsmul2 u N) (B.smul l₂ (B.zero2 x)) := (htr2 hy _).symm.trans (heq_of_eq e₂)
    refine (B.nsmul1_hcongr rfl hy N a2).trans ?_
    rw [B.nsmul1_smul]
    exact hsmH _ hx rfl _ _ ((B.nsmul1_zero2 x N).trans (congr_arg_heq B.zero2 hx))
  have key := eq_of_heq (L.symm.trans ((heq_of_eq (B.nsmul_comm u N N)).trans Rr))
  rw [hz] at key
  rw [div_pow, inj _ _ _ key, div_self']
end ReciprocityTheory.PGsh.BX

-- Prove2me | solution 1 for P2M_Formalism_IndefR_Fin_Four_IsLev_Heisenberg__83ee5bc11300
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:50:57.904151+00:00
-- url     : https://prove2.me/submissions/360a951a-053f-454e-afb8-bb37c0c177e9

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hY hXY hχl hχr hχ0 hLL
namespace Formalism.IndefR.Fin.Four
namespace IsLev
theorem _root_.solution {k m : ℕ} {G : V} (hG : IsLev ρ L X Y k G) {u : W} (hu : u ∈ Y) (hmu : m • u ∈ L) :
    IsLev ρ L X Y (k * m) (ρ u G) := by
  have c0 : ∀ y, χ 0 y = 1 := fun y => by
    have h := hχl 0 0 y
    rw [add_zero] at h
    exact mul_right_cancel₀ (hχ0 0 y) (by rw [one_mul]; exact h.symm)
  have c0' : ∀ t, χ t 0 = 1 := fun t => by
    have h := hχr t 0 0
    rw [add_zero] at h
    exact mul_right_cancel₀ (hχ0 t 0) (by rw [one_mul]; exact h.symm)
  have cl : ∀ (n : ℕ) t y, χ (n • t) y = χ t y ^ n := by
    intro n t y
    induction n with
    | zero => simp [c0]
    | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
  have cr : ∀ (n : ℕ) t y, χ t (n • y) = χ t y ^ n := by
    intro n t y
    induction n with
    | zero => simp [c0']
    | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have hx : ρ ((k * m) • v) G = G := by
      rw [← smul_smul]
      exact hG.1 _ (AddSubgroup.nsmul_mem _ hv m)
    have hmuY : m • u ∈ L ⊓ Y := AddSubgroup.mem_inf.2 ⟨hmu, AddSubgroup.nsmul_mem _ hu m⟩
    have hchi : χ ((k * m) • v) u = 1 := by
      rw [cl, mul_comm, pow_mul, ← cr, hLL v hv _ hmuY, one_pow]
    have hc := hXY ((k * m) • v) (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.1 hv).2 _) u hu
    calc ρ ((k * m) • v) (ρ u G) = (ρ ((k * m) • v) * ρ u) G := rfl
      _ = (χ ((k * m) • v) u • (ρ u * ρ ((k * m) • v))) G := by rw [hc]
      _ = ρ u G := by rw [hchi, one_smul, Module.End.mul_apply, hx]
  · have hx : ρ ((k * m) • v) G = G := by
      rw [← smul_smul]
      exact hG.2 _ (AddSubgroup.nsmul_mem _ hv m)
    have hy : (k * m) • v ∈ Y := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.1 hv).2 _
    have comm : ρ ((k * m) • v) * ρ u = ρ u * ρ ((k * m) • v) := by
      rw [← hY _ hy _ hu, ← hY _ hu _ hy, add_comm]
    calc ρ ((k * m) • v) (ρ u G) = (ρ ((k * m) • v) * ρ u) G := rfl
      _ = (ρ u * ρ ((k * m) • v)) G := by rw [comm]
      _ = ρ u G := by rw [Module.End.mul_apply, hx]
end IsLev
end Formalism.IndefR.Fin.Four

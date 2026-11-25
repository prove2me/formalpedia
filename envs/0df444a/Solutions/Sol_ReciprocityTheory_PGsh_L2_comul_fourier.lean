-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.comul_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:45.113003+00:00
-- url     : https://prove2.me/submissions/82ad6329-f821-4581-9b5b-dae9355d76b0

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
import Theorems.Thm_ReciprocityTheory_PGsh_L2_char_expand
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_dualLat_spanCols_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private theorem mem_dualLat_iff_pairing_integral {X : Type} [Fintype X] {M : Submodule R (X → C)} {u : X → C} :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl
private theorem mem_intFun_iff_pairing {X : Type} {f : X → C} :
    f ∈ intFun (C := C) R X ↔ ∀ x, ∃ r : R, algebraMap R C r = f x := Iff.rfl
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h')
    (AA : HopfOrder (C := C) R N) (B : Matrix N N C) (hB : IsUnit B.det)
    (hAA : AA.carrier = Submodule.span R (Set.range fun j x => B x j))
    (u : N → C) (hu : u ∈ dualLat AA.carrier) :
    addPull R H (fourier (R := R) (fun h a => e h a) u) ∈
      tensorSpan R ((dualLat AA.carrier).map (fourier (R := R) fun h a => e h a)) := by
  have hg : ∀ i, (fun a => u a * B a i) ∈ dualLat AA.carrier := by
    intro i
    rw [mem_dualLat_iff_pairing_integral]
    intro f hf
    have hcol : (fun x => B x i) ∈ AA.carrier := by
      rw [hAA]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_pairing_integral.1 hu) _ (AA.mul_mem _ _ hcol hf)
    refine ⟨r, hr.trans (Finset.sum_congr rfl fun a _ => ?_)⟩
    simp only [Pi.mul_apply]
    ring
  have hk : ∀ i, (fun x => B⁻¹ i x) ∈ dualLat AA.carrier := by
    intro i
    rw [hAA, mem_dualLat_spanCols_iff, mem_intFun_iff_pairing]
    intro j
    show ∃ r : R, algebraMap R C r = (B⁻¹ * B) i j
    rw [Matrix.nonsing_inv_mul B hB, Matrix.one_apply]
    by_cases hij : i = j
    · exact ⟨1, by simp [hij]⟩
    · exact ⟨0, by simp [hij]⟩
  have hsplit : addPull R H (fourier (R := R) (fun h a => e h a) u) =
      ∑ i, fun p : H × H => fourier (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1 *
        fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by
    funext p
    rw [Finset.sum_apply]
    simp only [addPull, LinearMap.funLeft_apply]
    calc fourier (R := R) (fun h a => e h a) u (p.1 + p.2)
        = ∑ a, u a * e p.1 a *
            ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 * B a i := by
          rw [fourier_apply' (R := R) (fun h a => e h a) u (p.1 + p.2)]
          refine Finset.sum_congr rfl fun a _ => ?_
          show u a * e (p.1 + p.2) a = _
          rw [he, AddChar.mul_apply, char_expand (R := R) e B hB p.2 a]
          ring
      _ = ∑ a, ∑ i, u a * B a i * e p.1 a *
            fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ i, ∑ a, u a * B a i * e p.1 a *
            fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := Finset.sum_comm
      _ = ∑ i, fourier (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1 *
            fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [fourier_apply' (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1, Finset.sum_mul]
  rw [hsplit]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
  exact ⟨_, Submodule.mem_map_of_mem (hg i), _, Submodule.mem_map_of_mem (hk i), rfl⟩
end ReciprocityTheory.PGsh.L2

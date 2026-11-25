-- Prove2me | solution 1 for PositivityTheory.RgUd.Form.U.Asm.exists_orth_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:08.153623+00:00
-- url     : https://prove2.me/submissions/ce01fd93-e550-4689-a955-be71662b259b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_HermitianForms_UnitaryLattices_UnitaryHypotheses_ExistsOrthOfFinset
import Theorems.Thm_PositivityTheory_RgUd_Form_U_Asm_mem_fixed_iff_irr
import Theorems.Thm_PositivityTheory_RgUd_Form_U_Asm_exists_orth_of_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd.Form.U.Asm
namespace PositivityTheory.RgUd.Form.U.Asm
theorem _root_.solution {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D]
    [Module ℂ D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y) (W : Submodule ℂ D)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (u : D) :
    ∃ w ∈ W, ∀ w' ∈ W, B (u - w) w' = 0 := by
  classical
  by_cases hu : u = 0
  · exact ⟨0, W.zero_mem, fun w' _ => by simp [hu]⟩
  let S : Subgroup G :=
    { carrier := {g | ρ g u = u}
      mul_mem' := by
        intro a b (ha : ρ a u = u) (hb : ρ b u = u)
        show ρ (a * b) u = u
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        show ρ 1 u = u
        simp
      inv_mem' := by
        intro a (ha : ρ a u = u)
        show ρ a⁻¹ u = u
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hA.1 u
  let K : Subgroup G := K₁ ⊓ S
  have hKo : IsOpen (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁o.inter hSo
  have hKc : IsCompact (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁c.inter_right (Subgroup.isClosed_of_isOpen S hSo)
  have hKS : ∀ k : K, ρ (k : G) u = u := fun k => (Subgroup.mem_inf.1 k.2).2
  have hBu : B u u ≠ 0 := by
    intro h; have := hBp u hu; rw [h] at this; simp at this
  have hχ : ∀ k : K, (χ k : ℂ) = 1 := by
    intro k
    have h := hBe k u u
    rw [hKS k] at h
    have h2 : ((χ k : ℂ) - 1) * B u u = 0 := by rw [sub_mul, ← h]; ring
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hBu
  have hBK : ∀ (k : K) x y, B (ρ (k : G) x) (ρ (k : G) y) = B x y := by
    intro k x y; rw [hBe, hχ, one_mul]
  have : FiniteDimensional ℂ (fixed ρ K) := hA.2 K hKo hKc
  let M : Submodule ℂ D := W ⊓ fixed ρ K
  have : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hs⟩ : M.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨w, hwM, hw⟩ := exists_orth_of_finset B hBp s u
  rw [hs] at hwM hw
  refine ⟨w, (Submodule.mem_inf.1 hwM).1, ?_⟩
  have huF : u - w ∈ fixed ρ K :=
    Submodule.sub_mem _ ((mem_fixed_iff_irr ρ K u).2 hKS) (Submodule.mem_inf.1 hwM).2
  have hfix := (mem_fixed_iff_irr ρ K _).1 huF
  intro w' hw'
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let f : K → D := fun k => ρ (k : G) w'
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k0
    refine ⟨(fun k : K => (k0 : G)⁻¹ * (k : G)) ⁻¹' {g | ρ g w' = w'},
      (hA.1 w').preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
    · simp
    · intro k hk
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk
      simp only [f]
      conv_lhs => rw [show (k : G) = (k0 : G) * ((k0 : G)⁻¹ * (k : G)) by group]
      rw [map_mul, Module.End.mul_apply, hk]
  obtain ⟨T, hTmem⟩ : ∃ T : Finset D, ∀ v, v ∈ T ↔ ∃ k : K, ρ (k : G) w' = v :=
    ⟨hf.range_finite.toFinset, fun v => by simp only [Set.Finite.mem_toFinset, Set.mem_range, f]⟩
  have hTst : ∀ h : K, ∀ v ∈ T, ρ (h : G) v ∈ T := by
    intro h v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    exact (hTmem _).2 ⟨h * k, by rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ h : K, ∀ v, ρ ((h⁻¹ : K) : G) (ρ (h : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hinv' : ∀ h : K, ∀ v, ρ (h : G) (ρ ((h⁻¹ : K) : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hsumF : ∑ v ∈ T, v ∈ M := by
    refine Submodule.mem_inf.2 ⟨Submodule.sum_mem _ (fun v hv => ?_), ?_⟩
    · obtain ⟨k, rfl⟩ := (hTmem v).1 hv; exact hW _ _ hw'
    · rw [mem_fixed_iff_irr]
      intro h
      rw [map_sum]
      exact Finset.sum_nbij' (fun v => ρ (h : G) v) (fun v => ρ ((h⁻¹ : K) : G) v) (hTst h) (hTst h⁻¹)
        (fun v _ => hinv h v) (fun v _ => hinv' h v) (fun v _ => rfl)
  have h0 := hw _ hsumF
  rw [map_sum] at h0
  have hterm : ∀ v ∈ T, B (u - w) v = B (u - w) w' := by
    intro v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    conv_lhs => rw [← hfix k]
    exact hBK k _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hcard : T.card ≠ 0 := Finset.card_ne_zero_of_mem ((hTmem w').2 ⟨1, by simp⟩)
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 hcard
  · exact h1
end PositivityTheory.RgUd.Form.U.Asm

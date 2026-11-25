-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.LocFam.denseDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:39.645682+00:00
-- url     : https://prove2.me/submissions/4e1eb7b0-8dcc-49b2-8c6b-5da3769c60a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_T2SpaceOfIsValuativeTopology
import Theorems.Thm_PI_ProdFormulaE_Tr_exists_approx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel Filter Topology
namespace PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F]
variable {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
private theorem exists_valuation_sub_lt_of_injective [Finite ι] (D : LocFam F ℓ ι) (hP : Function.Injective D.P)
    (k : ∀ i, D.K i) (γ : ∀ i, (ValueGroupWithZero (D.K i))ˣ) :
    ∃ x : F, ∀ i, valuation (D.K i) (D.ιF i x - k i) < γ i := by
  have hl : ∀ i, Tendsto (fun N : ℕ => D.ιF i ((ℓ : F) ^ N)) atTop (𝓝 0) := by
    intro i
    have h0 : Tendsto (fun N : ℕ => (ℓ : ℚ_[ℓ]) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have h1 := ((D.cont i).tendsto 0).comp h0
    rw [map_zero] at h1
    convert h1 using 1
    funext N
    simp
  have hev : ∀ᶠ N in atTop, ∀ i, valuation (D.K i) (D.ιF i ((ℓ : F) ^ N)) < γ i := by
    rw [Filter.eventually_all]
    intro i
    exact hl i ((IsValuativeTopology.hasBasis_nhds_zero (D.K i)).mem_of_mem (i := γ i) trivial)
  obtain ⟨N, hN⟩ := hev.exists
  have hb : ∀ i, ∃ b : F, valuation (D.K i) (D.ιF i b - k i) < γ i := by
    intro i
    obtain ⟨_, hz, b, rfl⟩ := mem_closure_iff_nhds.1 (D.dense i (k i)) _
      ((IsValuativeTopology.hasBasis_nhds (k i)).mem_of_mem (i := γ i) trivial)
    exact ⟨b, hz⟩
  choose b hb using hb
  have hc : ((ℓ : F) ^ N) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  obtain ⟨x, hx⟩ := exists_approx D.P hP b _ hc
  refine ⟨x, fun i => ?_⟩
  have h1 : valuation (D.K i) (D.ιF i (x - b i)) ≤ valuation (D.K i) (D.ιF i ((ℓ : F) ^ N)) :=
    (Valuation.vle_iff_le (valuation (D.K i))).1 ((D.val i _ _).2 (hx i))
  have h2 : D.ιF i x - k i = D.ιF i (x - b i) + (D.ιF i (b i) - k i) := by
    rw [map_sub]
    ring
  rw [h2]
  exact Valuation.map_add_lt _ (lt_of_le_of_lt h1 (hN i)) (hb i)
end PI.ProdFormulaE.Tr
end
end

set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel Filter Topology
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F]
variable {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
namespace PI.ProdFormulaE.Tr
namespace LocFam
theorem _root_.solution [Finite ι] (D : LocFam F ℓ ι) (hP : Function.Injective D.P) :
    DenseRange (fun x : F => fun i => D.ιF i x) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨k, hk⟩
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU k hk
  have hγ : ∀ i, ∃ γ : (ValueGroupWithZero (D.K i))ˣ,
      i ∈ I → {z | valuation (D.K i) (z - k i) < γ} ⊆ u i := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨γ, -, hγ⟩ :=
        (IsValuativeTopology.hasBasis_nhds (k i)).mem_iff.1 ((hu i hi).1.mem_nhds (hu i hi).2)
      exact ⟨γ, fun _ => hγ⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose γ hγ using hγ
  obtain ⟨x, hx⟩ := exists_valuation_sub_lt_of_injective D hP k γ
  exact ⟨_, hIU (fun i hi => hγ i hi (hx i)), x, rfl⟩
end LocFam
end PI.ProdFormulaE.Tr

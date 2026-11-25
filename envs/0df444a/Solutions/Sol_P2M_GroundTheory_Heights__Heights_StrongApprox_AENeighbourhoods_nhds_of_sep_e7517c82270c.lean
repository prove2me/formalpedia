-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_of_sep_e7517c82270c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:35.870296+00:00
-- url     : https://prove2.me/submissions/56140cdd-d39d-4d3f-a473-f2e2f932e66d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_zero_finiteAdele_2c19578e73bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_exists_repr_of_int_c51e6e82ed72
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
theorem _root_.solution [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)]
    (hsep : ∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b) (N : ℕ)
    (U : Set (Matrix (Fin N) (Fin N) (AE F E))) (hU : U ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ M : Matrix (Fin N) (Fin N) (AE F E),
      (∀ i j, (∀ v ∈ S, compAt E v (M i j) = 0) ∧ ∀ v ∉ S, compAt E v (M i j) ∈ intAt E v) →
      M ∈ U := by
  classical
  have := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  let ι := Fin N × Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let Ψ : (ι → FiniteAdeleRing (𝓞 F) F) → Matrix (Fin N) (Fin N) (AE F E) :=
    fun X => Matrix.of fun i j => ∑ l, X (i, j, l) • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l)
  have hΨ : Continuous Ψ :=
    continuous_pi fun i => continuous_pi fun j =>
      continuous_finsetSum _ fun l _ => (continuous_apply (i, j, l)).smul
        (continuous_const : Continuous fun _ : ι → FiniteAdeleRing (𝓞 F) F =>
          ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l))
  have hΨ0 : Ψ 0 = 0 := by ext i j; simp [Ψ]
  have hpre : Ψ ⁻¹' U ∈ 𝓝 (0 : ι → FiniteAdeleRing (𝓞 F) F) :=
    hΨ.continuousAt.preimage_mem_nhds (by rw [hΨ0]; exact hU)
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  obtain ⟨S, hS⟩ := nhds_zero_finiteAdele (Filter.iInter_mem.2 fun k : ι => ht k)
  refine ⟨S, fun M hM => ?_⟩
  choose X hX0 hXI hXeq using fun i j => exists_repr_of_int hsep S (hM i j).1 (hM i j).2
  have hmem : (fun k : ι => X k.1 k.2.1 k.2.2) ∈ I.pi t := fun k _ =>
    Set.mem_iInter.1 (hS _ (hX0 _ _ _) (hXI _ _ _)) k
  have hM' : Ψ (fun k : ι => X k.1 k.2.1 k.2.2) = M := by
    ext i j
    rw [hXeq i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_tmul', smul_eq_mul, mul_one]
  have hfin := hsub hmem
  rw [Set.mem_preimage, hM'] at hfin
  exact hfin
end GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods

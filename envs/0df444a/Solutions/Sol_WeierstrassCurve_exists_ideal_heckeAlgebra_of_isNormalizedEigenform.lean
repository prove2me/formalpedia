-- Prove2me | solution 1 for WeierstrassCurve.exists_ideal_heckeAlgebra_of_isNormalizedEigenform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8441f186-a3a4-5dbc-ad20-0c76a4b52d92

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeT
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_of_isNormalizedEigenform
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

open CuspForm ModularForm CongruenceSubgroup

namespace E0aSol

variable {L : ℕ} [NeZero L] {S₀ : Set ℕ}

lemma exists_smul_of_mem {g : CuspForm (Gamma0 L) 2} (hg : g.IsNormalizedEigenform)
    {x : Module.End ℂ (CuspForm (Gamma0 L) 2)} (hx : x ∈ heckeAlgebra L 2 S₀) :
    ∃ c : ℂ, x g = c • g := by
  obtain ⟨-, hTU⟩ := (CuspForm.isNormalizedEigenform_iff_heckeT g).mp hg
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
    · refine ⟨ModularFormClass.qCoeff g ℓ, ?_⟩
      apply DFunLike.coe_injective
      simp only [CuspForm.coe_heckeTLin_apply, (hTU ℓ hℓ).1 hℓN]
      rfl
    · refine ⟨ModularFormClass.qCoeff g q, ?_⟩
      apply DFunLike.coe_injective
      simp only [CuspForm.coe_heckeULin_apply, (hTU q hq).2 hqN]
      rfl
  | algebraMap r =>
    refine ⟨(r : ℂ), ?_⟩
    rw [Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]
  | add x y hx hy ihx ihy =>
    obtain ⟨c, hc⟩ := ihx
    obtain ⟨d, hd⟩ := ihy
    exact ⟨c + d, by rw [LinearMap.add_apply, hc, hd, add_smul]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨c, hc⟩ := ihx
    obtain ⟨d, hd⟩ := ihy
    exact ⟨c * d, by rw [Module.End.mul_apply, hd, map_smul, hc, smul_smul, mul_comm d c]⟩

variable {g : CuspForm (Gamma0 L) 2}

noncomputable def eigenvalueAt (hg : g.IsNormalizedEigenform)
    (x : ↥(heckeAlgebra L 2 S₀)) : ℂ :=
  (exists_smul_of_mem hg x.2).choose

lemma eigenvalueAt_spec (hg : g.IsNormalizedEigenform) (x : ↥(heckeAlgebra L 2 S₀)) :
    (x : Module.End ℂ (CuspForm (Gamma0 L) 2)) g = eigenvalueAt hg x • g :=
  (exists_smul_of_mem hg x.2).choose_spec

lemma eigenvalueAt_eq (hg : g.IsNormalizedEigenform) {x : ↥(heckeAlgebra L 2 S₀)} {c : ℂ}
    (h : (x : Module.End ℂ (CuspForm (Gamma0 L) 2)) g = c • g) :
    eigenvalueAt hg x = c := by
  have h2 := eigenvalueAt_spec hg x
  rw [h] at h2
  have h3 := sub_eq_zero.mpr h2.symm
  rw [← sub_smul] at h3
  rcases smul_eq_zero.mp h3 with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hg.ne_zero

noncomputable def eigenchar (hg : g.IsNormalizedEigenform) :
    ↥(heckeAlgebra L 2 S₀) →+* ℂ :=
  RingHom.mk'
    { toFun := eigenvalueAt hg
      map_one' := eigenvalueAt_eq hg (by simp)
      map_mul' := fun x y => by
        refine eigenvalueAt_eq hg ?_
        calc ((x * y : ↥(heckeAlgebra L 2 S₀)) :
              Module.End ℂ (CuspForm (Gamma0 L) 2)) g
            = (x : Module.End ℂ _) ((y : Module.End ℂ _) g) := rfl
          _ = (x : Module.End ℂ _) (eigenvalueAt hg y • g) := by
              rw [eigenvalueAt_spec hg y]
          _ = eigenvalueAt hg y • ((x : Module.End ℂ _) g) := map_smul _ _ _
          _ = (eigenvalueAt hg x * eigenvalueAt hg y) • g := by
              rw [eigenvalueAt_spec hg x, smul_smul, mul_comm] }
    (fun x y => by
      refine eigenvalueAt_eq hg ?_
      calc ((x + y : ↥(heckeAlgebra L 2 S₀)) :
            Module.End ℂ (CuspForm (Gamma0 L) 2)) g
          = (x : Module.End ℂ _) g + (y : Module.End ℂ _) g := rfl
        _ = (eigenvalueAt hg x + eigenvalueAt hg y) • g := by
            rw [eigenvalueAt_spec hg x, eigenvalueAt_spec hg y, add_smul])

@[scoped simp] lemma eigenchar_apply (hg : g.IsNormalizedEigenform)
    (x : ↥(heckeAlgebra L 2 S₀)) : eigenchar hg x = eigenvalueAt hg x := rfl

lemma eigenchar_T (hg : g.IsNormalizedEigenform)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L) (hℓS : ℓ ∉ S₀) :
    eigenchar hg (heckeAlgebra.T hℓ hℓL hℓS) = ModularFormClass.qCoeff g ℓ := by
  refine eigenvalueAt_eq hg ?_
  obtain ⟨-, hTU⟩ := (CuspForm.isNormalizedEigenform_iff_heckeT g).mp hg
  rw [heckeAlgebra.coe_T]
  apply DFunLike.coe_injective
  simp only [CuspForm.coe_heckeTLin_apply, (hTU ℓ hℓ).1 hℓL]
  rfl

lemma eigenchar_mem_integralClosure (hg : g.IsNormalizedEigenform)
    (x : ↥(heckeAlgebra L 2 S₀)) :
    eigenchar hg x ∈ integralClosure ℤ ℂ := by
  haveI : Module.Finite ℤ ↥(heckeAlgebra L 2 S₀) :=
    CuspForm.moduleFinite_heckeAlgebra_two L S₀
  have hx : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
  exact hx.map (eigenchar hg).toIntAlgHom

end E0aSol
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_of_isNormalizedEigenform.E0aSol"

open E0aSol in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (p : ℕ) (W : WeierstrassCurve ℤ) {L : ℕ} [NeZero L] (S₀ : Set ℕ)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNormalizedEigenform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S₀ →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∃ 𝔪₂ : Ideal (heckeAlgebra L 2 S₀), 𝔪₂.IsMaximal ∧
      (p : heckeAlgebra L 2 S₀) ∈ 𝔪₂ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ L),
        W.IsGoodPrimeFor ℓ →
          heckeAlgebra.T hℓ hℓN hℓS -
            ((W.apOfModel ℓ : ℤ) : heckeAlgebra L 2 S₀) ∈ 𝔪₂ := by
  classical
  let χ : ↥(heckeAlgebra L 2 S₀) →+* ↥(integralClosure ℤ ℂ) :=
    (eigenchar hg).codRestrict (integralClosure ℤ ℂ).toSubring
      (eigenchar_mem_integralClosure hg)
  letI : Algebra ↥(heckeAlgebra L 2 S₀) ↥(integralClosure ℤ ℂ) := χ.toAlgebra
  haveI : IsScalarTower ℤ ↥(heckeAlgebra L 2 S₀) ↥(integralClosure ℤ ℂ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsIntegral ↥(heckeAlgebra L 2 S₀) ↥(integralClosure ℤ ℂ) :=
    ⟨fun z => IsIntegral.tower_top (integralClosure.isIntegral z)⟩
  haveI := h𝔪
  refine ⟨Ideal.comap χ 𝔪, ?_, ?_, ?_⟩
  · exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (R := ↥(heckeAlgebra L 2 S₀)) 𝔪
  · have hp' : χ (p : ↥(heckeAlgebra L 2 S₀)) = (p : ↥(integralClosure ℤ ℂ)) :=
      map_natCast χ p
    simpa [Ideal.mem_comap, hp'] using hp𝔪
  · intro ℓ hℓ hℓS hℓN hgood
    obtain ⟨a, ha, hamem⟩ := hcong ℓ hℓ hgood hℓS
    have hχT : χ (heckeAlgebra.T hℓ hℓN hℓS) = a := by
      apply Subtype.coe_injective
      show eigenchar hg (heckeAlgebra.T hℓ hℓN hℓS) = (a : ℂ)
      rw [eigenchar_T hg hℓ hℓN hℓS, ha]
    rw [Ideal.mem_comap, map_sub, hχT, map_intCast]
    exact hamem

end S_WeierstrassCurve_exists_ideal_heckeAlgebra_of_isNormalizedEigenform
end P2MW
export P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_of_isNormalizedEigenform (solution)

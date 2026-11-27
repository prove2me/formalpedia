-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_proof_273300c6540e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:34.228801+00:00
-- url     : https://prove2.me/submissions/69ffb7d7-6d31-4523-b68f-bdf72b7cb18d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineCoeffsFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_natCast_mul_c5f7da338ffb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_mul_of_dvd_56198ea8cf87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_nat_mul_isIntegral_0b76cb35c68e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_common_multiple_06ca60e23aba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_den_of_fg_b9c8a444fbec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_mem_intMultiples_818cdd960c3a
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IdealClassesFinite_proof_91676186b289
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineCoeffsFG_proof_53ed2500803f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LinePairOrbitsFinite_proof_09504d4235de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_map_of_fg_a33155c6d1a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_le_fg_fd0431823b0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_finite_sandwich_bc5e518da275
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
open LineNormalForm
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace LineNormalForm
theorem _root_.solution (h : HermitianForm F E W) : LineNormalForm.Statement h := by
  classical
  intro D
  set B := h.toSesq

  have cc : ∀ a : E, conjHom F E (conjHom F E a) = a := fun a => conj_conj (F := F) a
  have ci : ∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (conjHom F E a) :=
    fun a ha => ha.map (conjHom F E).toIntAlgHom
  have cn : ∀ N : ℕ, conjHom F E (N : E) = N := fun N => map_natCast _ N
  have hsym : ∀ x y, conjHom F E (B x y) = B y x := fun x y => h.isSymm.eq x y
  have hsmul : ∀ (a : E) x y, B (a • x) y = conjHom F E a * B x y := by
    intro a x y
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]

  obtain ⟨T, hT, hTJ⟩ := IdealClassesFinite.proof E
  obtain ⟨d, hd, hdT⟩ := exists_common_multiple hT.toFinset
    (fun J n => J.FG → J ≠ ⊥ → (∀ j ∈ J, IsIntegral ℤ ((n : E) * j)) ∧
        ∃ j₀ ∈ J, j₀ ≠ 0 ∧ IsIntegral ℤ ((n : E) * j₀⁻¹))
    (fun J a b hJ hab hfg hne => by
      obtain ⟨h1, j₀, hj₀, hj₀0, h2⟩ := hJ hfg hne
      exact ⟨fun j hj => isIntegral_mul_of_dvd (h1 j hj) hab, j₀, hj₀, hj₀0,
        isIntegral_mul_of_dvd h2 hab⟩)
    (fun J _ => by
      by_cases hfg : J.FG
      · by_cases hne : J = ⊥
        · exact ⟨1, one_pos, fun _ h => absurd hne h⟩
        · obtain ⟨a, ha, haJ⟩ := exists_den_of_fg hfg
          obtain ⟨j₀, hj₀, hj₀0⟩ : ∃ j₀ ∈ J, j₀ ≠ 0 := by
            by_contra hc
            push Not at hc
            exact hne ((AddSubgroup.eq_bot_iff_forall J).2 hc)
          obtain ⟨b, hb, hbj⟩ := exists_nat_mul_isIntegral j₀⁻¹
          exact ⟨a * b, Nat.mul_pos ha hb, fun _ _ =>
            ⟨fun j hj => isIntegral_mul_of_dvd (haJ j hj) (dvd_mul_right a b), j₀, hj₀, hj₀0,
              isIntegral_mul_of_dvd hbj (dvd_mul_left b a)⟩⟩
      · exact ⟨1, one_pos, fun h _ => absurd h hfg⟩)
  set m := D.factorial with hm_def
  have hm : 0 < m := Nat.factorial_pos D
  have hmd : 0 < m * d := Nat.mul_pos hm hd
  set k := 2 * m * d ^ 3 with hk_def
  have hk : 0 < k := by positivity
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hk0 : (k : E) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  refine ⟨{A | intMultiples E (m * d) ≤ A ∧ (∀ x ∈ A, (m * d * d) • x ∈ intMultiples E (m * d)) ∧
      A.FG} ×ˢ {A | intMultiples E k ≤ A ∧ (∀ x ∈ A, (k * d) • x ∈ intMultiples E k) ∧ A.FG},
    (finite_sandwich _ (by positivity)).prod (finite_sandwich _ (by positivity)), k * d,
    Nat.mul_pos hk hd, ?_⟩
  intro La l hD hl
  have hLat := hD.isLattice
  have hint : ∀ x ∈ La, ∀ y ∈ La, IsIntegral ℤ (B x y) := fun x hx y hy =>
    (mem_integralClosure_iff ℤ E).1 (hD.integral x hx y hy)
  have hsm : ∀ {a : E}, IsIntegral ℤ a → ∀ {x}, x ∈ La → a • x ∈ La :=
    fun ha _ hx => hLat.smul_mem ⟨_, ha⟩ _ hx

  have hdual : ∀ y, (∀ x ∈ La, IsIntegral ℤ (B y x)) → (m : E) • y ∈ La := by
    intro y hy
    have hy' : y ∈ dualLattice h La := fun x hx => (mem_integralClosure_iff ℤ E).2 (hy x hx)
    obtain ⟨t, ht⟩ : La.relIndex (dualLattice h La) ∣ m := Nat.dvd_factorial (Nat.pos_of_ne_zero hD.index_ne_zero) hD.index_le
    rw [Nat.cast_smul_eq_nsmul, ht, mul_nsmul]
    exact La.nsmul_mem (La.nsmul_relIndex_mem hy') t

  obtain ⟨v₁, hv₁l, hv₁0⟩ : ∃ v₁ ∈ l, v₁ ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h0 => ?_
    have := hl.1
    rw [h0, finrank_bot] at this
    exact zero_ne_one this
  set J₁ := La.map (B v₁).toAddMonoidHom with hJ₁_def
  have hJ₁fg : J₁.FG := fg_map_of_fg hLat.fg _
  have hJ₁ne : J₁ ≠ ⊥ := by
    intro h0
    apply hv₁0
    apply h.nonsingular.1
    rw [map_zero]
    refine LinearMap.ext_on hLat.span_eq_top (fun x hx => ?_)
    have : B v₁ x ∈ J₁ := ⟨x, hx, rfl⟩
    rw [h0, AddSubgroup.mem_bot] at this
    simpa using this
  have hJ₁st : ∀ a : 𝓞 E, ∀ x ∈ J₁, (a : E) * x ∈ J₁ := by
    rintro a _ ⟨x, hx, rfl⟩
    exact ⟨(a : E) • x, hLat.smul_mem a x hx, by simp⟩
  obtain ⟨J, hJT, c, hc, hJ₁⟩ := hTJ J₁ hJ₁fg hJ₁ne hJ₁st
  have hJfg : J.FG := by
    refine fg_of_le_fg (fun j hj => ?_) (fg_map_of_fg hJ₁fg (AddMonoidHom.mulLeft c⁻¹))
    refine ⟨c * j, ?_, ?_⟩
    · rw [hJ₁]; exact ⟨j, hj, rfl⟩
    · simp [← mul_assoc, inv_mul_cancel₀ hc]
  have hJne : J ≠ ⊥ := by
    intro h0
    exact hJ₁ne (by rw [hJ₁, h0, AddSubgroup.map_bot])
  obtain ⟨hdJ, j₀, hj₀J, hj₀0, hdj₀⟩ := hdT J (hT.mem_toFinset.2 hJT) hJfg hJne
  set v := conjHom F E c⁻¹ • v₁ with hv_def
  have hBv : ∀ x, B v x = c⁻¹ * B v₁ x := by
    intro x; rw [hv_def, hsmul, cc]
  have hvJ : ∀ x ∈ La, B v x ∈ J := by
    intro x hx
    have : B v₁ x ∈ J₁ := ⟨x, hx, rfl⟩
    rw [hJ₁] at this
    obtain ⟨j, hj, hjx⟩ := this
    rw [hBv, ← hjx]
    simpa [← mul_assoc, inv_mul_cancel₀ hc] using hj
  have hJv : ∀ j ∈ J, ∃ x ∈ La, B v x = j := by
    intro j hj
    have : c * j ∈ J₁ := by rw [hJ₁]; exact ⟨j, hj, rfl⟩
    obtain ⟨x, hx, hxj⟩ := this
    refine ⟨x, hx, ?_⟩
    rw [hBv]
    have hxj' : B v₁ x = c * j := hxj
    rw [hxj', ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hv0 : v ≠ 0 := smul_ne_zero ((map_ne_zero _).2 (inv_ne_zero hc)) hv₁0
  have hvl : v ∈ l := l.smul_mem _ hv₁l
  have hvv : B v v = 0 := hl.2 v hvl v hvl
  have hdvx : ∀ x ∈ La, IsIntegral ℤ ((d : E) * B v x) := fun x hx => hdJ _ (hvJ x hx)
  obtain ⟨x₁, hx₁, hx₁j⟩ := hJv j₀ hj₀J
  have hcj₀ : conjHom F E j₀ ≠ 0 := (map_ne_zero _).2 hj₀0

  have hIlo : intMultiples E (m * d) ≤ lineCoeffs (E := E) La v := by
    intro x hx
    rw [mem_intMultiples] at hx
    generalize ho : ((m * d : ℕ) : E)⁻¹ * x = o at hx
    have hxo : x = (m : E) * ((d : E) * o) := by
      rw [← ho]; push_cast; field_simp
    change x • v ∈ La
    rw [hxo, ← smul_smul]
    refine hdual _ fun z hz => ?_
    rw [hsmul, map_mul, cn, mul_comm (d : E), mul_assoc]
    exact (ci o hx).mul (hdvx z hz)
  have hIup : ∀ a ∈ lineCoeffs (E := E) La v, IsIntegral ℤ ((d : E) * a) := by
    intro a ha
    have ha' : a • v ∈ La := ha
    have h1 : IsIntegral ℤ (conjHom F E a * j₀) := by
      have := hint _ ha' x₁ hx₁
      rwa [hsmul, hx₁j] at this
    have h2 : conjHom F E ((d : E) * a) = conjHom F E a * j₀ * ((d : E) * j₀⁻¹) := by
      rw [map_mul, cn]; field_simp
    have := ci _ ((h1.mul hdj₀))
    rwa [← h2, cc] at this

  set q := B x₁ x₁ / (conjHom F E j₀ * j₀) with hq_def
  have hq : conjHom F E q = q := by
    rw [hq_def, map_div₀, hsym, map_mul, cc, mul_comm j₀]
  have hq2 : conjHom F E (q / 2) = q / 2 := by rw [map_div₀, hq, map_ofNat]
  have hqi : IsIntegral ℤ ((d : E) ^ 2 * q) := by
    have e1 : (d : E) ^ 2 * q = B x₁ x₁ * ((d : E) * j₀⁻¹) * conjHom F E ((d : E) * j₀⁻¹) := by
      rw [hq_def, map_mul, map_inv₀, cn]; field_simp
    rw [e1]
    exact ((hint _ hx₁ _ hx₁).mul hdj₀).mul (ci _ hdj₀)
  set w := j₀⁻¹ • x₁ - (q / 2) • v with hw_def
  have hBw : ∀ x, B w x = conjHom F E j₀⁻¹ * B x₁ x - q / 2 * B v x := by
    intro x
    rw [hw_def, LinearMap.map_sub₂, hsmul, hsmul, hq2]
  have hvw : B v w = 1 := by
    rw [hw_def, (B v).map_sub, (B v).map_smul, (B v).map_smul, smul_eq_mul, smul_eq_mul, hx₁j, hvv, mul_zero,
      sub_zero, inv_mul_cancel₀ hj₀0]
  have hww : B w w = 0 := by
    rw [hBw, hvw]
    have hx₁v : B x₁ v = conjHom F E j₀ := by rw [← hsym, hx₁j]
    rw [hw_def, (B x₁).map_sub, (B x₁).map_smul, (B x₁).map_smul, smul_eq_mul, smul_eq_mul, hx₁v,
      map_inv₀, hq_def]
    field_simp
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvw
    exact zero_ne_one hvw

  have hKlo : intMultiples E k ≤ lineCoeffs (E := E) La w := by
    intro b hb
    rw [mem_intMultiples] at hb
    generalize ho : ((k : ℕ) : E)⁻¹ * b = o at hb
    have hbo : b = (k : E) * o := by rw [← ho]; field_simp
    change b • w ∈ La
    rw [hw_def, smul_sub, smul_smul, smul_smul]
    refine La.sub_mem (hsm ?_ hx₁) ?_
    · have : b * j₀⁻¹ = ((2 * m * d ^ 2 : ℕ) : E) * o * ((d : E) * j₀⁻¹) := by
        rw [hbo, hk_def]; push_cast; ring
      rw [this]
      exact (isIntegral_natCast_mul hb).mul hdj₀
    · apply hIlo
      rw [mem_intMultiples]
      have : ((m * d : ℕ) : E)⁻¹ * (b * (q / 2)) = (d : E) ^ 2 * q * o := by
        rw [hbo, hk_def]; push_cast; field_simp
      rw [this]
      exact hqi.mul hb
  have hKup : ∀ b ∈ lineCoeffs (E := E) La w, IsIntegral ℤ ((d : E) * b) := by
    intro b hb
    have hb' : b • w ∈ La := hb
    have := hdvx _ hb'
    rwa [map_smul, smul_eq_mul, hvw, mul_one] at this
  refine ⟨v, w, hvl, ⟨hvv, hww, hvw⟩, ⟨⟨hIlo, fun a ha => ?_, LineCoeffsFG.proof W La v hLat.fg hv0⟩,
    ⟨hKlo, fun b hb => ?_, LineCoeffsFG.proof W La w hLat.fg hw0⟩⟩, fun x hx => ⟨?_, ?_⟩⟩
  · rw [nsmul_eq_mul, mem_intMultiples]
    have : ((m * d : ℕ) : E)⁻¹ * ((m * d * d : ℕ) * a) = (d : E) * a := by
      push_cast; field_simp
    rw [this]; exact hIup a ha
  · rw [nsmul_eq_mul, mem_intMultiples]
    have : ((k : ℕ) : E)⁻¹ * ((k * d : ℕ) * b) = (d : E) * b := by
      push_cast; field_simp
    rw [this]; exact hKup b hb

  · apply hIlo
    rw [mem_intMultiples]
    have : ((m * d : ℕ) : E)⁻¹ * (((k * d : ℕ) : E) * B w x) =
        2 * (d : E) ^ 2 * conjHom F E ((d : E) * j₀⁻¹) * B x₁ x - (d : E) ^ 2 * q * ((d : E) * B v x) := by
      rw [hBw, hk_def, map_mul, cn]; push_cast; field_simp
    rw [this]
    refine IsIntegral.sub ?_ (hqi.mul (hdvx x hx))
    have h2 : IsIntegral ℤ (2 * (d : E) ^ 2) := by
      have := isIntegral_natCast_mul (n := 2 * d ^ 2) (isIntegral_one : IsIntegral ℤ (1 : E))
      simpa using this
    exact (h2.mul (ci _ hdj₀)).mul (hint _ hx₁ _ hx)
  · apply hKlo
    rw [mem_intMultiples]
    have : ((k : ℕ) : E)⁻¹ * (((k * d : ℕ) : E) * B v x) = (d : E) * B v x := by
      push_cast; field_simp
    rw [this]; exact hdvx x hx
end LineNormalForm
end GroundTheory.Heights₂.Heights.FiniteCovolume

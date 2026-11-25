-- Prove2me | solution 1 for PI.AlgValsFin.W.assemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:55.666476+00:00
-- url     : https://prove2.me/submissions/eae22300-e400-409d-9856-8583e8d825e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_IsIntegralOfMemCompo
import Theorems.Thm_PI_AlgValsFin_W_prod_mem_compo
import Theorems.Thm_PI_AlgValsFin_W_isIntegral_of_mem_compo
import Theorems.Thm_PI_AlgValsFin_W_eq_of_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution : Assemble L := by
  classical
  intro hTors hKey hPow hSame χ s m hm
  obtain ⟨N, hN0, hN⟩ := hTors χ
  obtain ⟨h, hh0, hk⟩ := hPow
  obtain ⟨ι, hι, c, hc⟩ := hSame
  haveI := hι
  have hz : ∀ r ∈ UFin L, ((χ.1 r : ℂˣ) : ℂ) ^ N = 1 := by
    intro r hr
    rw [← Units.val_pow_eq_pow_val, hN r hr, Units.val_one]
  let U := {i : ι // ∃ v, c v = i ∧ χ.UnrAt v}
  let f : U → ℂ := fun i => χ.valTw s i.2.choose
  let S : Set ℂ := ((Polynomial.nthRoots N (1 : ℂ)).toFinset : Set ℂ) ∪ Set.range f
  haveI : Finite S := ((Set.toFinite _).union (Set.finite_range f)).to_subtype
  have hA : ∀ v, χ.UnrAt v → ∃ P ∈ compo L, ∃ z : ℂ, z ^ N = 1 ∧ χ.valTw s v ^ h * (P * z) = 1 := by
    intro v hv
    obtain ⟨kv, hkv⟩ := hk v
    have h1 : ∀ u, u ∉ ({v} : Finset (HeightOneSpectrum (𝓞 L))) → ordF u kv = 0 := by
      intro u hu
      rw [hkv u, if_neg (fun h' => hu (Finset.mem_singleton.mpr h'))]
    have h2 : ∀ u ∈ ({v} : Finset (HeightOneSpectrum (𝓞 L))), χ.UnrAt u := by
      intro u hu
      rw [Finset.mem_singleton.mp hu]
      exact hv
    obtain ⟨r, hr, e⟩ := hKey χ s m hm kv {v} h1 h2
    refine ⟨_, prod_mem_compo m (kv : L), _, hz r hr, ?_⟩
    rw [Finset.prod_singleton, hkv v, if_pos rfl, zpow_natCast] at e
    rw [← mul_assoc]
    exact e
  let C : IntermediateField ℚ ℂ := compo L ⊔ IntermediateField.adjoin ℚ S
  have hCcompo : compo L ≤ C := le_sup_left
  have hSsub : ∀ x ∈ S, x ∈ C := fun x hx => (le_sup_right : IntermediateField.adjoin ℚ S ≤ C)
    (IntermediateField.subset_adjoin ℚ S hx)
  have hmu : ∀ z : ℂ, z ^ N = 1 → z ∈ C := fun z hz' =>
    hSsub z (Or.inl (by simp [Polynomial.mem_nthRoots hN0, hz']))
  have hf : ∀ i : U, f i ∈ C := fun i => hSsub _ (Or.inr ⟨i, rfl⟩)
  have hval : ∀ v, χ.UnrAt v → χ.valTw s v ∈ C := by
    intro v hv
    have hex : ∃ v', c v' = c v ∧ χ.UnrAt v' := ⟨v, rfl, hv⟩
    have hw := hex.choose_spec
    have hwC : χ.valTw s hex.choose ∈ C := hf ⟨c v, hex⟩
    by_cases hvw : v = hex.choose
    · rw [hvw]
      exact hwC
    · obtain ⟨k, hkk⟩ := hc v hex.choose hw.1.symm
      have h1 : ∀ u, u ∉ ({v, hex.choose} : Finset (HeightOneSpectrum (𝓞 L))) → ordF u k = 0 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
        rw [hkk u, if_neg hu.1, if_neg hu.2, sub_zero]
      have h2 : ∀ u ∈ ({v, hex.choose} : Finset (HeightOneSpectrum (𝓞 L))), χ.UnrAt u := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hv
        · exact hw.2
      obtain ⟨r, hr, e⟩ := hKey χ s m hm k {v, hex.choose} h1 h2
      have o1 : ordF v k = 1 := by rw [hkk]; simp [hvw]
      have o2 : ordF hex.choose k = -1 := by rw [hkk]; simp [Ne.symm hvw]
      rw [Finset.prod_pair hvw, o1, o2, zpow_one, zpow_neg_one] at e
      rw [eq_of_key e]
      exact C.mul_mem hwC (C.inv_mem (C.mul_mem (hCcompo (prod_mem_compo m (k : L))) (hmu _ (hz r hr))))
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    intro x hx
    rcases hx with hx | ⟨i, rfl⟩
    · have hx' : x ^ N = 1 := by simpa [Polynomial.mem_nthRoots hN0] using hx
      exact IsIntegral.of_pow hN0 (by rw [hx']; exact isIntegral_one)
    · obtain ⟨P, hP, z, hzN, e⟩ := hA _ i.2.choose_spec.2
      have hpow : (f i) ^ (h * N) ∈ compo L := by
        have e1 : (f i) ^ h = (P * z)⁻¹ := eq_inv_of_mul_eq_one_left e
        rw [pow_mul, e1, inv_pow, mul_pow, hzN, mul_one]
        exact inv_mem (pow_mem hP N)
      exact IsIntegral.of_pow (Nat.mul_pos hh0 hN0) (isIntegral_of_mem_compo hpow)
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hint
  haveI hC : FiniteDimensional ℚ C := IntermediateField.finiteDimensional_sup _ _
  refine ⟨C.toSubfield, ?_, fun v hv => ⟨⟨χ.valTw s v, hval v hv⟩, rfl⟩⟩
  let e : C ≃ₗ[ℚ] C.toSubfield :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun q x => rfl
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  exact LinearEquiv.finiteDimensional e
end PI.AlgValsFin.W

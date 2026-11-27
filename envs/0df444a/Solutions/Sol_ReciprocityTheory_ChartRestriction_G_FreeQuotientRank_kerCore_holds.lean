-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.kerCore_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:25:26.426822+00:00
-- url     : https://prove2.me/submissions/8972c1f7-0ac9-45bb-bed7-cfda8281670e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_KerCoreSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_KerCorePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_exists_finset_inf_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_galAct_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finrank_baseSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_galAct_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_galoisDescent_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution : KerCoreStatement := by
  intro K _ _ V _ _ _ W Fam hkill hdet henl
  classical

  let S : Set (Submodule K V) := {N | ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
    (f : V →ₗ[K] K₁), Fam K₁ f ∧ N = LinearMap.ker f}
  obtain ⟨t, htS, htinf⟩ := exists_finset_inf_eq S
  have hmem : ∀ N : t, ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
      (f : V →ₗ[K] K₁), Fam K₁ f ∧ (N : Submodule K V) = LinearMap.ker f := fun N => htS N.2
  choose Ki fKi nfKi aKi fi hfam hNker using hmem
  have hWinf : t.inf id = W := by
    apply le_antisymm
    · intro v hv
      apply hdet v
      intro K₁ _ _ _ f hf
      have := htinf (LinearMap.ker f) ⟨K₁, inferInstance, inferInstance, inferInstance, f, hf, rfl⟩ hv
      exact this
    · refine Finset.le_inf fun N hN => ?_
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      show W ≤ N
      rw [h1]
      exact hkill _ _ (hfam ⟨N, hN⟩)
  have hWmem : ∀ v, v ∈ W ↔ ∀ N : t, fi N v = 0 := by
    intro v
    rw [← hWinf, Finset.inf_eq_iInf]
    simp only [Submodule.mem_iInf, id]
    constructor
    · intro hv N
      have h1 := hv N N.2
      rw [hNker N] at h1
      exact h1
    · intro h N hN
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      rw [h1]
      exact h ⟨N, hN⟩

  let Ω := AlgebraicClosure K
  have hfinKi : ∀ N, FiniteDimensional K (Ki N) := fun N =>
    Module.Finite.of_restrictScalars_finite ℚ K (Ki N)
  let ιi : ∀ N : t, Ki N →ₐ[K] Ω := fun N =>
    have := hfinKi N
    IsAlgClosed.lift
  let M : IntermediateField K Ω := ⨆ N : t, (ιi N).fieldRange
  have hMfin : FiniteDimensional K M := by
    have : ∀ N : t, FiniteDimensional K (ιi N).fieldRange := fun N =>
      haveI := hfinKi N
      (AlgHom.equivFieldRange (ιi N)).toLinearEquiv.finiteDimensional
    exact IntermediateField.finiteDimensional_iSup_of_finite
  let L : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hLfin : FiniteDimensional K L := inferInstance
  have hLgal : IsGalois K L := inferInstance
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hQL : FiniteDimensional ℚ L := Module.Finite.trans K L
  have hnfL : NumberField L := ⟨⟩

  have hrange : ∀ N (x : Ki N), ιi N x ∈ L := fun N x =>
    hML (le_iSup (fun N : t => (ιi N).fieldRange) N ⟨x, rfl⟩)
  let e0 : ∀ N : t, Ki N →ₐ[K] L := fun N => (ιi N).codRestrict L.toSubalgebra (hrange N)

  have hg : ∀ (N : t) (e : Ki N →ₐ[K] L), ∃ g : V →ₗ[K] L, Fam L g ∧ ∀ v, g v = e (fi N v) :=
    fun N e => henl (Ki N) L e (fi N) (hfam N)
  choose g hgfam hgval using hg
  let gh : (Σ N : t, (Ki N →ₐ[K] L)) → Module.Dual L (L ⊗[K] V) :=
    fun p => (g p.1 p.2).liftBaseChange L
  have hgh1 : ∀ p v, gh p ((1 : L) ⊗ₜ[K] v) = g p.1 p.2 v := fun p v =>
    LinearMap.liftBaseChange_one_tmul _ _ _
  let Kc : Submodule L (L ⊗[K] V) := ⨅ p, LinearMap.ker (gh p)

  have hkey : ∀ (σ : L ≃ₐ[K] L) (N : t) (e : Ki N →ₐ[K] L) (x : L ⊗[K] V),
      gh ⟨N, e⟩ (galAct σ x) = σ (gh ⟨N, (σ.symm.toAlgHom).comp e⟩ x) := by
    intro σ N e x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      simp only [gh, galAct_tmul, LinearMap.liftBaseChange_tmul, hgval, smul_eq_mul, map_mul,
        AlgHom.comp_apply]
      congr 1
      exact (σ.apply_symm_apply _).symm
    | add y z hy hz => simp only [map_add, hy, hz]
  have hstab : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ Kc, galAct σ x ∈ Kc := by
    intro σ x hx
    rw [Submodule.mem_iInf] at hx ⊢
    rintro ⟨N, e⟩
    rw [LinearMap.mem_ker, hkey, LinearMap.mem_ker.mp (hx ⟨N, _⟩), map_zero]
  have hGD := galoisDescent_holds K L V Kc hstab
  have hkP : kPoints Kc = W := by
    ext v
    rw [hWmem]
    show (1 : L) ⊗ₜ[K] v ∈ Kc ↔ _
    rw [Submodule.mem_iInf]
    constructor
    · intro h N
      have h1 := LinearMap.mem_ker.mp (h ⟨N, e0 N⟩)
      have h2 : e0 N (fi N v) = 0 := by
        have h3 := hgval N (e0 N) v
        rw [← h3]
        simpa [hgh1] using h1
      exact (e0 N).toRingHom.injective (by simpa using h2)
    · intro h p
      rw [LinearMap.mem_ker, hgh1, hgval p.1 p.2 v, h p.1, map_zero]
  have hKc : Kc = baseSpan L W := by rw [hGD, hkP]

  let G : Set (Module.Dual L (L ⊗[K] V)) := Set.range gh
  obtain ⟨t', ht'sub, ht'span, ht'li⟩ := exists_linearIndependent L G
  have ht'fin : t'.Finite := ht'li.setFinite
  have : Fintype t' := ht'fin.fintype
  set ρ := Fintype.card t' with hρ
  let eT := Fintype.equivFin t'
  have hpick : ∀ i : Fin ρ, ∃ p, gh p = (eT.symm i : Module.Dual L (L ⊗[K] V)) :=
    fun i => ht'sub (eT.symm i).2
  choose pk hpk using hpick
  let cfL : Fin ρ → Module.Dual L (L ⊗[K] V) := fun i => (eT.symm i : Module.Dual L (L ⊗[K] V))
  have hcomm : ∀ x : L ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ Kc := by
    intro x
    constructor
    · intro h
      rw [Submodule.mem_iInf]
      intro p
      rw [LinearMap.mem_ker]
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun φ hφ => ?_
        have := h (eT ⟨φ, hφ⟩)
        simpa [cfL] using this
      have hmem : gh p ∈ Submodule.span L t' := ht'span ▸ Submodule.subset_span ⟨p, rfl⟩
      simpa using hsp hmem
    · intro hx i
      rw [Submodule.mem_iInf] at hx
      show (eT.symm i : Module.Dual L (L ⊗[K] V)) x = 0
      rw [← hpk i]
      exact LinearMap.mem_ker.mp (hx (pk i))
  have hcoan : (Submodule.span L t').dualCoannihilator = Kc := by
    ext x
    rw [Submodule.mem_dualCoannihilator, ← hcomm]
    constructor
    · intro h i
      exact h _ (Submodule.subset_span (eT.symm i).2)
    · intro h φ hφ
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun ψ hψ => ?_
        have := h (eT ⟨ψ, hψ⟩)
        simpa [cfL] using this
      simpa using hsp hφ
  have hWfd : FiniteDimensional K W := inferInstance
  have hdim : Module.finrank K W + ρ = Module.finrank K V := by
    have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span L t')
    rw [hcoan, hKc, finrank_baseSpan L W, Module.finrank_baseChange] at h1
    have h2 : Module.finrank L (Submodule.span L t') = ρ := by
      rw [hρ, finrank_span_set_eq_card ht'li, Set.toFinset_card]
    omega
  refine ⟨L, inferInstance, hnfL, inferInstance, ρ, fun i => g (pk i).1 (pk i).2, cfL,
    fun i => hgfam _ _, fun i v => ?_, fun x => ?_, hdim⟩
  · rw [show cfL i = gh (pk i) from (hpk i).symm, hgh1]
  · rw [hcomm, hKc]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

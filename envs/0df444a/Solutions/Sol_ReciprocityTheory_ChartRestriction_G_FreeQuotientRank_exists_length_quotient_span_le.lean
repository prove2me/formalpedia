-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_length_quotient_span_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:13:52.095315+00:00
-- url     : https://prove2.me/submissions/33df74c2-fc8d-4dc8-9f0f-74203201fd51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotShiftPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotShiftPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_QuotShiftPfH_addVal_eq_ord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open IsDedekindDomain QuotShiftPfH
private theorem ordAt_mul_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [map_mul, WithZero.log_mul ((v.valuation F).ne_zero_iff.mpr hx)
    ((v.valuation F).ne_zero_iff.mpr hy)]
  ring
private theorem ordAt_zpow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (x : F) (k : ℤ) :
    ordAt v (x ^ k) = k * ordAt v x := by
  unfold ordAt
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring
private theorem ordAt_prod_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {ι : Type} (S : Finset ι)
    (f : ι → F) (hf : ∀ i, f i ≠ 0) : ordAt v (∏ i ∈ S, f i) = ∑ i ∈ S, ordAt v (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    unfold ordAt
    rw [map_one]
    rfl
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ordAt_mul_rationality v (hf a) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i), ih]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open IsDedekindDomain QuotShiftPfH
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (hL : QuotLocalStatement) {R F : Type} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (Q : Type)
    [AddCommGroup Q] [Module (Rv F v) Q] (ρ : ℕ) (hb : Nonempty (Module.Basis (Fin ρ) (Rv F v) Q))
    (c : Fin ρ → (Q →ₗ[Rv F v] F)) (s : Fin ρ → ℝ) (β : ℝ) (th : Fin ρ → Q)
    (hc : ∀ i q, c i q ≠ 0 → -β ≤ (ordAt v (c i q) : ℝ) + s i)
    (hdet : (Matrix.of fun i j => c i (th j)).det ≠ 0) :
    ∃ n : ℕ, Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) = n ∧
      (n : ℝ) ≤ (ordAt v (Matrix.of fun i j => c i (th j)).det : ℝ) + ∑ i, s i + ρ * β := by
  classical

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Rv F v)
  set π : F := (ϖ : F) with hπdef
  have hπ0 : π ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hπ1 : ordAt v π = 1 := by
    have h1 := (addVal_eq_ord v ϖ hπ0).symm.trans (IsDiscreteValuationRing.addVal_uniformizer hϖ)
    have h2 : (ordAt v π).toNat = 1 := by exact_mod_cast h1
    have h3 := ord_nonneg v ϖ hπ0
    omega

  have hne : ∀ i, ∃ q, c i q ≠ 0 := by
    intro i
    by_contra h
    push_neg at h
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [h])

  have hex : ∀ i, ∃ μ : ℤ, (∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = μ) ∧
      ∀ q, c i q ≠ 0 → μ ≤ ordAt v (c i q) := by
    intro i
    obtain ⟨lb, ⟨q, hq, rfl⟩, hlb⟩ := Int.exists_least_of_bdd
      (P := fun z => ∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = z)
      ⟨⌈-β - s i⌉, by
        rintro z ⟨q, hq, rfl⟩
        refine Int.ceil_le.mpr ?_
        have := hc i q hq
        linarith⟩
      (by obtain ⟨q, hq⟩ := hne i; exact ⟨_, q, hq, rfl⟩)
    exact ⟨_, ⟨q, hq, rfl⟩, fun q' hq' => hlb _ ⟨q', hq', rfl⟩⟩
  choose μ hμ1 hμ2 using hex
  have hμβ : ∀ i, -(μ i : ℝ) ≤ β + s i := by
    intro i
    obtain ⟨q, hq, hqμ⟩ := hμ1 i
    have := hc i q hq
    rw [hqμ] at this
    linarith

  have hmem : ∀ i q, π ^ (-μ i) * c i q ∈ Rv F v := by
    intro i q
    by_cases hq : c i q = 0
    · rw [hq, mul_zero]; exact (Rv F v).zero_mem
    · refine (mem_Rv_iff_ord v (mul_ne_zero (zpow_ne_zero _ hπ0) hq)).mpr ?_
      rw [ordAt_mul_rationality v (zpow_ne_zero _ hπ0) hq, ordAt_zpow, hπ1]
      have := hμ2 i q hq
      linarith
  let c' : Fin ρ → (Q →ₗ[Rv F v] Rv F v) := fun i =>
    { toFun := fun q => ⟨π ^ (-μ i) * c i q, hmem i q⟩
      map_add' := fun a b => by ext; simp [mul_add]
      map_smul' := fun r q => by
        ext
        simp only [LinearMap.map_smul, RingHom.id_apply, Subring.coe_mul, Subring.smul_def,
          smul_eq_mul]
        ring }
  have hmap : ((Matrix.of fun i j => c' i (th j)).map (Rv F v).subtype) =
      Matrix.diagonal (fun i => π ^ (-μ i)) * Matrix.of fun i j => c i (th j) := by
    ext i j
    simp [Matrix.diagonal_mul, c']
  have hdetF : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (∏ i, π ^ (-μ i)) * (Matrix.of fun i j => c i (th j)).det := by
    have := RingHom.map_det (Rv F v).subtype (Matrix.of fun i j => c' i (th j))
    simp only [RingHom.mapMatrix_apply] at this
    rw [show (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (Rv F v).subtype (Matrix.of fun i j => c' i (th j)).det from rfl, this, hmap,
      Matrix.det_mul, Matrix.det_diagonal]
  have hP0 : (∏ i, π ^ (-μ i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ hπ0
  have hdF0 : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) ≠ 0 := by
    rw [hdetF]; exact mul_ne_zero hP0 hdet
  have hdet' : (Matrix.of fun i j => c' i (th j)).det ≠ 0 := fun h => hdF0 (by rw [h]; rfl)
  have hlen := hL (Rv F v) Q ρ hb c' th hdet'
  rw [addVal_eq_ord v _ hdF0] at hlen
  have hord : ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      ∑ i, -μ i + ordAt v (Matrix.of fun i j => c i (th j)).det := by
    rw [hdetF, ordAt_mul_rationality v hP0 hdet, ordAt_prod_rationality v _ _ fun i => zpow_ne_zero _ hπ0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ordAt_zpow, hπ1, mul_one]
  have hnn := ord_nonneg v _ hdF0
  have htop : Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hlen
  refine ⟨(Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat,
    (ENat.coe_toNat htop).symm, ?_⟩
  have hle : (Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F)).toNat := by
    rw [← ENat.coe_toNat htop] at hlen
    exact_mod_cast hlen
  have hle' : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℝ) ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) : ℝ) := by
    have : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℤ) ≤
        ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) := by omega
    exact_mod_cast this
  rw [hord] at hle'
  push_cast at hle'
  have hsum : ∑ i, (-(μ i : ℝ)) ≤ ∑ i, (β + s i) := Finset.sum_le_sum fun i _ => hμβ i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  linarith
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

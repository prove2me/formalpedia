-- Prove2me | solution 1 for TwistedUnipotentTerm.integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/360b102e-adf9-5bbd-906c-0acb5e769b79

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace KcLogShellTrace

section LocalField

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

local notation "Fu" => u.adicCompletion F
local notation "𝒪u" => u.adicCompletionIntegers F

theorem exists_valued_eq_exp_neg_one : ∃ π : Fu, Valued.v π = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer F u
  refine ⟨algebraMap F Fu π, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]

theorem exists_valued_eq_exp (n : ℤ) : ∃ c : Fu, Valued.v c = WithZero.exp n ∧ c ≠ 0 := by
  obtain ⟨π, hπ⟩ := exists_valued_eq_exp_neg_one F u
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  refine ⟨π ^ (-n), ?_, zpow_ne_zero _ hπ0⟩
  rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]; simp

theorem natCard_residueField :
    Nat.card (IsLocalRing.ResidueField 𝒪u) = Ideal.absNorm u.asIdeal := by
  classical
  set f : 𝓞 F →+* IsLocalRing.ResidueField 𝒪u :=
    (IsLocalRing.residue 𝒪u).comp (algebraMap (𝓞 F) 𝒪u) with hf
  have hfs : Function.Surjective f := NumberField.AdelicHaar.residue_algebraMap_surjective (𝓞 F) F u
  have hker : RingHom.ker f = u.asIdeal := by
    refine (Ideal.IsMaximal.eq_of_le u.isMaximal (RingHom.ker_ne_top f) fun a ha => ?_).symm
    rw [RingHom.mem_ker]
    exact NumberField.AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 F) F u ha
  have e2 : (𝓞 F ⧸ u.asIdeal) ≃+* IsLocalRing.ResidueField 𝒪u :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hfs)
  rw [← Nat.card_congr e2.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem residue_eq_residue_iff (a b : 𝒪u) :
    IsLocalRing.residue 𝒪u a = IsLocalRing.residue 𝒪u b ↔ Valued.v ((a : Fu) - b) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one]
  push_cast
  exact Iff.rfl

def vball (n : ℤ) : Set Fu := {y | Valued.v y ≤ WithZero.exp n}

theorem mem_vball_iff (n : ℤ) (y : Fu) : y ∈ vball F u n ↔ Valued.v y ≤ WithZero.exp n := Iff.rfl

theorem vball_eq_preimage {c : Fu} {n : ℤ} (hc : Valued.v c = WithZero.exp (-n)) :
    vball F u n = (fun y => c * y) ⁻¹' (𝒪u : Set Fu) := by
  ext y
  rw [mem_vball_iff, Set.mem_preimage, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    map_mul, hc, WithZero.exp_neg, inv_mul_le_iff₀ (WithZero.exp_pos), mul_one]

theorem isOpen_vball (n : ℤ) : IsOpen (vball F u n) := by
  obtain ⟨c, hc, -⟩ := exists_valued_eq_exp F u (-n)
  rw [vball_eq_preimage F u hc]
  exact ((NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 F) F).out u).preimage (continuous_const_mul _)

theorem valued_le_exp_neg_one_of_lt_one {y : Fu} (hy : Valued.v y < 1) : Valued.v y ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : Valued.v y = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.log_le_iff_le_exp h0]
    have h : WithZero.log (Valued.v y) < 0 := by
      rw [WithZero.log_lt_iff_lt_exp h0, WithZero.exp_zero]; exact hy
    omega

theorem valued_le_exp_sub_one_of_lt {y : Fu} {ℓ : ℤ} (hy : Valued.v y < WithZero.exp ℓ) :
    Valued.v y ≤ WithZero.exp (ℓ - 1) := by
  by_cases h0 : Valued.v y = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.log_le_iff_le_exp h0]
    have h : WithZero.log (Valued.v y) < ℓ := by
      rw [WithZero.log_lt_iff_lt_exp h0]; exact hy
    omega

theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (k : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp k) = e ^ k := by
  rw [WithZeroMulInt.toNNReal_neg_apply he (WithZero.exp_ne_zero)]
  congr 1

theorem norm_eq_zpow_log {y : Fu} (hy : y ≠ 0) :
    ‖y‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (WithZero.log (Valued.v y)) := by
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [NumberField.FinitePlace.norm_def]
  conv_lhs => rw [← WithZero.exp_log hv]
  rw [toNNReal_exp]
  push_cast
  rfl

theorem log_modulus_eq (y : Fu) :
    Real.log (LanglandsTunnell.TateLocal.modulus y : ℝ) =
      ((WithZero.log (Valued.v y) : ℤ) : ℝ) * Real.log (Ideal.absNorm u.asIdeal : ℝ) := by
  by_cases hy : y = 0
  · subst hy
    simp
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm, norm_eq_zpow_log F u hy,
    Real.log_zpow]

private theorem _root_.KcLogShellTrace.one_lt_absNorm : 1 < Ideal.absNorm u.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm u

p2m_export "KcLogShellTrace" "one_lt_absNorm"

theorem valued_algebraMap_coe (b : 𝓞 F) : Valued.v (algebraMap F Fu (b : F)) = u.intValuation b := by
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F) u]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _

end LocalField

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

abbrev E : (L ⊗[K] v.adicCompletion K) ≃ₐ[L] (Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) :=
  HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

open scoped TensorProduct.RightActions in

theorem continuous_coord (w' : v.Extension (𝓞 L)) : Continuous fun x : L ⊗[K] v.adicCompletion K => E K L v x w' :=
  (continuous_apply w').comp (AutomorphicForm.semiLocalHomeomorph K L v).continuous

def shell (n : ℤ) : Set (L ⊗[K] v.adicCompletion K) :=
  {x | (∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L) ∧
    E K L v x w ∈ vball L w.1 n}

theorem mem_shell_iff (n : ℤ) (x : L ⊗[K] v.adicCompletion K) :
    x ∈ shell K L v w n ↔ (∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L) ∧
      Valued.v (E K L v x w) ≤ WithZero.exp n := Iff.rfl

open scoped TensorProduct.RightActions in
theorem isOpen_shell (n : ℤ) : IsOpen (shell K L v w n) := by
  have h1 : IsOpen {x : L ⊗[K] v.adicCompletion K |
      ∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L} := by
    haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
    have : {x : L ⊗[K] v.adicCompletion K |
        ∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L} =
        ⋂ w' : v.Extension (𝓞 L), {x | w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L} := by
      ext x; simp
    rw [this]
    refine isOpen_iInter_of_finite fun w' => ?_
    by_cases hw' : w' = w
    · have : {x : L ⊗[K] v.adicCompletion K | w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L} = Set.univ := by
        ext x; simp [hw']
      rw [this]; exact isOpen_univ
    · have : {x : L ⊗[K] v.adicCompletion K | w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L} =
          (fun x => E K L v x w') ⁻¹' (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L)) := by
        ext x; simp [hw']
      rw [this]
      exact ((NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 L) L).out w'.1).preimage
        (continuous_coord K L v w')
  have h2 : IsOpen {x : L ⊗[K] v.adicCompletion K | E K L v x w ∈ vball L w.1 n} :=
    (isOpen_vball L w.1 n).preimage (continuous_coord K L v w)
  exact h1.inter h2

open scoped TensorProduct.RightActions in
theorem measurableSet_shell [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (n : ℤ) : MeasurableSet (shell K L v w n) :=
  (isOpen_shell K L v w n).measurableSet

open scoped TensorProduct.RightActions in

theorem shell_zero_eq : shell K L v w 0 = AutomorphicForm.semiLocalIntegers K L v := by
  ext x
  rw [mem_shell_iff, AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers,
    Set.mem_univ_pi, WithZero.exp_zero]
  constructor
  · rintro ⟨h1, h2⟩ w'
    by_cases hw' : w' = w
    · subst hw'
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h2
    · exact h1 w' hw'
  · intro h
    exact ⟨fun w' _ => h w', (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h w)⟩

theorem setOf_forall_mem_eq_shell_zero :
    {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), E K L v x w' ∈ w'.1.adicCompletionIntegers L} =
      shell K L v w 0 := by
  ext x
  rw [Set.mem_setOf_eq, mem_shell_iff, WithZero.exp_zero]
  constructor
  · intro h
    exact ⟨fun w' _ => h w', (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h w)⟩
  · rintro ⟨h1, h2⟩ w'
    by_cases hw' : w' = w
    · subst hw'
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h2
    · exact h1 w' hw'

open scoped TensorProduct.RightActions in
theorem isCompact_shell_zero : IsCompact (shell K L v w 0) := by
  rw [shell_zero_eq]; exact AutomorphicForm.isCompact_semiLocalIntegers K L v

theorem zero_mem_shell (n : ℤ) : (0 : L ⊗[K] v.adicCompletion K) ∈ shell K L v w n := by
  rw [mem_shell_iff]
  simp only [map_zero, Pi.zero_apply, zero_mem, implies_true, true_and]
  exact zero_le'

theorem add_mem_shell {n : ℤ} {x y : L ⊗[K] v.adicCompletion K} (hx : x ∈ shell K L v w n)
    (hy : y ∈ shell K L v w n) : x + y ∈ shell K L v w n := by
  rw [mem_shell_iff] at hx hy ⊢
  refine ⟨fun w' hw' => ?_, ?_⟩
  · rw [map_add, Pi.add_apply]; exact add_mem (hx.1 w' hw') (hy.1 w' hw')
  · rw [map_add, Pi.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le hx.2 hy.2)

theorem neg_mem_shell {n : ℤ} {x : L ⊗[K] v.adicCompletion K} (hx : x ∈ shell K L v w n) :
    -x ∈ shell K L v w n := by
  rw [mem_shell_iff] at hx ⊢
  refine ⟨fun w' hw' => ?_, ?_⟩
  · rw [map_neg, Pi.neg_apply]; exact neg_mem (hx.1 w' hw')
  · rw [map_neg, Pi.neg_apply, Valuation.map_neg]; exact hx.2

theorem sub_mem_shell {n : ℤ} {x y : L ⊗[K] v.adicCompletion K} (hx : x ∈ shell K L v w n)
    (hy : y ∈ shell K L v w n) : x - y ∈ shell K L v w n := by
  rw [sub_eq_add_neg]; exact add_mem_shell K L v w hx (neg_mem_shell K L v w hy)

theorem shell_mono {m n : ℤ} (h : m ≤ n) : shell K L v w m ⊆ shell K L v w n := by
  intro x hx
  rw [mem_shell_iff] at hx ⊢
  exact ⟨hx.1, hx.2.trans (WithZero.exp_le_exp.2 h)⟩

def tvec (c : w.1.adicCompletion L) : L ⊗[K] v.adicCompletion K := by
  classical
  exact (E K L v).symm (Pi.single w c : Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)

theorem E_tvec_self (c : w.1.adicCompletion L) : E K L v (tvec K L v w c) w = c := by
  classical
  unfold tvec
  rw [AlgEquiv.apply_symm_apply]
  exact Pi.single_eq_same _ _

theorem E_tvec_of_ne (c : w.1.adicCompletion L) {w' : v.Extension (𝓞 L)} (hw' : w' ≠ w) :
    E K L v (tvec K L v w c) w' = 0 := by
  classical
  unfold tvec
  rw [AlgEquiv.apply_symm_apply]
  exact Pi.single_eq_of_ne hw' _

theorem sub_tvec_mem_shell_iff (n : ℤ) (x : L ⊗[K] v.adicCompletion K) (c : w.1.adicCompletion L) :
    x - tvec K L v w c ∈ shell K L v w n ↔
      (∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L) ∧
        Valued.v (E K L v x w - c) ≤ WithZero.exp n := by
  have hne : ∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v (x - tvec K L v w c) w' = E K L v x w' := fun w' hw' => by
    rw [map_sub, Pi.sub_apply, E_tvec_of_ne K L v w c hw', sub_zero]
  have hw : E K L v (x - tvec K L v w c) w = E K L v x w - c := by
    rw [map_sub, Pi.sub_apply, E_tvec_self]
  rw [mem_shell_iff, hw]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' hw' => by rw [← hne w' hw']; exact h1 w' hw', h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' hw' => by rw [hne w' hw']; exact h1 w' hw', h2⟩

open scoped TensorProduct.RightActions in

theorem measure_shell_succ [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] (n : ℕ) :
    ν (shell K L v w (n + 1 : ℕ)) = (Ideal.absNorm w.1.asIdeal : ENNReal) * ν (shell K L v w n) := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)

  set Ow := w.1.adicCompletionIntegers L with hOw
  haveI : Finite (IsLocalRing.ResidueField Ow) := inferInstance
  letI : Fintype (IsLocalRing.ResidueField Ow) := Fintype.ofFinite _
  have hsurj : Function.Surjective (IsLocalRing.residue Ow) := IsLocalRing.residue_surjective
  set s : IsLocalRing.ResidueField Ow → Ow := Function.surjInv hsurj with hs
  have hs_mk : ∀ ρ, IsLocalRing.residue Ow (s ρ) = ρ := fun ρ => Function.surjInv_eq hsurj ρ

  obtain ⟨c, hcv, hc0⟩ := exists_valued_eq_exp L w.1 (-(n + 1 : ℕ) : ℤ)
  have hcinv : Valued.v c⁻¹ = WithZero.exp ((n + 1 : ℕ) : ℤ) := by
    rw [map_inv₀, hcv, WithZero.exp_neg, inv_inv]

  set piece : IsLocalRing.ResidueField Ow → Set (L ⊗[K] v.adicCompletion K) := fun ρ =>
    (fun x => -tvec K L v w (c⁻¹ * (s ρ : w.1.adicCompletion L)) + x) ⁻¹' shell K L v w n with hpiece
  have hmem_piece : ∀ ρ x, x ∈ piece ρ ↔
      (∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L) ∧
        Valued.v (E K L v x w - c⁻¹ * (s ρ : w.1.adicCompletion L)) ≤ WithZero.exp (n : ℤ) := by
    intro ρ x
    simp only [hpiece, Set.mem_preimage]
    rw [neg_add_eq_sub, sub_tvec_mem_shell_iff]

  have hkey : ∀ (y : w.1.adicCompletion L) (t : Ow),
      Valued.v (y - c⁻¹ * (t : w.1.adicCompletion L)) =
        WithZero.exp ((n + 1 : ℕ) : ℤ) * Valued.v (c * y - (t : w.1.adicCompletion L)) := by
    intro y t
    have : y - c⁻¹ * (t : w.1.adicCompletion L) = c⁻¹ * (c * y - (t : w.1.adicCompletion L)) := by
      field_simp
    rw [this, map_mul, hcinv]
  have hexp : WithZero.exp ((n + 1 : ℕ) : ℤ) * WithZero.exp (-1 : ℤ) = WithZero.exp (n : ℤ) := by
    rw [← WithZero.exp_add]; congr 1; push_cast; ring

  have hcover : (⋃ ρ, piece ρ) = shell K L v w (n + 1 : ℕ) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨ρ, hρ⟩
      rw [hmem_piece] at hρ
      refine ⟨hρ.1, ?_⟩
      have hsplit : E K L v x w = (E K L v x w - c⁻¹ * (s ρ : w.1.adicCompletion L)) +
          c⁻¹ * (s ρ : w.1.adicCompletion L) := by ring
      show Valued.v (E K L v x w) ≤ WithZero.exp ((n + 1 : ℕ) : ℤ)
      rw [hsplit]
      refine (Valuation.map_add _ _ _).trans (max_le (hρ.2.trans ?_) ?_)
      · rw [WithZero.exp_le_exp]; push_cast; linarith
      · rw [map_mul, hcinv]
        calc WithZero.exp ((n + 1 : ℕ) : ℤ) * Valued.v (s ρ : w.1.adicCompletion L)
            ≤ WithZero.exp ((n + 1 : ℕ) : ℤ) * 1 := mul_le_mul_right (s ρ).2 _
          _ = WithZero.exp ((n + 1 : ℕ) : ℤ) := mul_one _
    · intro hx
      rw [mem_shell_iff] at hx

      have hy : c * E K L v x w ∈ Ow := by
        rw [hOw, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hcv, WithZero.exp_neg,
          inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
        exact hx.2
      set y : Ow := ⟨c * E K L v x w, hy⟩ with hy'
      refine ⟨IsLocalRing.residue Ow y, ?_⟩
      rw [hmem_piece]
      refine ⟨hx.1, ?_⟩
      rw [hkey, ← hexp]
      refine mul_le_mul_right (valued_le_exp_neg_one_of_lt_one L w.1 ?_) _
      have h := (residue_eq_residue_iff L w.1 y (s (IsLocalRing.residue Ow y))).1 (hs_mk _).symm
      exact h

  have hdisj : Pairwise (Function.onFun Disjoint piece) := by
    intro ρ ρ' hρρ'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [hmem_piece] at hx hx'
    apply hρρ'
    rw [← hs_mk ρ, ← hs_mk ρ', residue_eq_residue_iff]
    have hd : Valued.v (c⁻¹ * ((s ρ : w.1.adicCompletion L) - (s ρ' : w.1.adicCompletion L))) ≤ WithZero.exp (n : ℤ) := by
      have : c⁻¹ * ((s ρ : w.1.adicCompletion L) - (s ρ' : w.1.adicCompletion L)) =
          (E K L v x w - c⁻¹ * (s ρ' : w.1.adicCompletion L)) + -(E K L v x w - c⁻¹ * (s ρ : w.1.adicCompletion L)) := by
        ring
      rw [this]
      refine (Valuation.map_add _ _ _).trans (max_le hx'.2 ?_)
      rw [Valuation.map_neg]; exact hx.2
    have hd' : Valued.v ((s ρ : w.1.adicCompletion L) - (s ρ' : w.1.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
      have : (s ρ : w.1.adicCompletion L) - (s ρ' : w.1.adicCompletion L) =
          c * (c⁻¹ * ((s ρ : w.1.adicCompletion L) - (s ρ' : w.1.adicCompletion L))) := by
        rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      rw [this, map_mul, hcv]
      calc WithZero.exp (-(n + 1 : ℕ) : ℤ) * Valued.v (c⁻¹ * ((s ρ : w.1.adicCompletion L) - (s ρ' : w.1.adicCompletion L)))
          ≤ WithZero.exp (-(n + 1 : ℕ) : ℤ) * WithZero.exp (n : ℤ) := mul_le_mul_right hd _
        _ = WithZero.exp (-1 : ℤ) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    calc Valued.v ((s ρ : w.1.adicCompletion L) - (s ρ' : w.1.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := hd'
      _ < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hmeas : ∀ ρ, MeasurableSet (piece ρ) := fun ρ =>
    (measurable_const_add _) (measurableSet_shell K L v w n)
  have hμ : ∀ ρ, ν (piece ρ) = ν (shell K L v w n) := fun ρ => measure_preimage_add ν _ _
  rw [← hcover, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, natCard_residueField L w.1]

open scoped TensorProduct.RightActions in

theorem measure_shell [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] (n : ℕ) :
    ν (shell K L v w n) = (Ideal.absNorm w.1.asIdeal : ENNReal) ^ n * ν (shell K L v w 0) := by
  induction n with
  | zero => simp
  | succ n ih => rw [measure_shell_succ, ih, pow_succ]; ring

open scoped TensorProduct.RightActions in
theorem measure_shell_zero_lt_top [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] : ν (shell K L v w 0) < ⊤ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact (isCompact_shell_zero K L v w).measure_lt_top

open scoped TensorProduct.RightActions in
theorem measure_shell_lt_top [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] (n : ℕ) : ν (shell K L v w n) < ⊤ := by
  rw [measure_shell]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.natCast_lt_top _)) (measure_shell_zero_lt_top K L v w ν)

def poleOrder (y : w.1.adicCompletion L) : ℕ := (WithZero.log (Valued.v y)).toNat

theorem poleOrder_le_iff (y : w.1.adicCompletion L) (n : ℕ) : poleOrder K L v w y ≤ n ↔ y ∈ vball L w.1 n := by
  rw [poleOrder, mem_vball_iff, Int.toNat_le]
  by_cases hy : y = 0
  · subst hy
    simp
  · have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    rw [WithZero.log_le_iff_le_exp hv]

def eshell (r : ℕ) : Set (L ⊗[K] v.adicCompletion K) :=
  {x | (∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L) ∧
    poleOrder K L v w (E K L v x w) = r}

theorem eshell_zero : eshell K L v w 0 = shell K L v w 0 := by
  ext x
  rw [eshell, Set.mem_setOf_eq, mem_shell_iff, ← Nat.le_zero, poleOrder_le_iff, mem_vball_iff, Nat.cast_zero]

theorem eshell_succ (r : ℕ) : eshell K L v w (r + 1) = shell K L v w (r + 1 : ℕ) \ shell K L v w r := by
  ext x
  rw [eshell, Set.mem_setOf_eq, Set.mem_diff, mem_shell_iff, mem_shell_iff, ← mem_vball_iff, ← mem_vball_iff,
    ← poleOrder_le_iff, ← poleOrder_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2.le⟩, fun h => by omega⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    have : ¬ poleOrder K L v w (E K L v x w) ≤ r := fun h => h3 ⟨h1, h⟩
    omega

theorem eshell_subset_shell (r : ℕ) : eshell K L v w r ⊆ shell K L v w r := by
  cases r with
  | zero => rw [eshell_zero, Nat.cast_zero]
  | succ r => rw [eshell_succ]; exact Set.diff_subset

theorem shell_mono_nat (r : ℕ) : shell K L v w r ⊆ shell K L v w (r + 1 : ℕ) :=
  shell_mono K L v w (by push_cast; linarith)

open scoped TensorProduct.RightActions in
theorem measurableSet_eshell [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (r : ℕ) : MeasurableSet (eshell K L v w r) := by
  cases r with
  | zero => rw [eshell_zero]; exact measurableSet_shell K L v w 0
  | succ r =>
    rw [eshell_succ]
    exact (measurableSet_shell K L v w _).diff (measurableSet_shell K L v w r)

open scoped TensorProduct.RightActions in
theorem measure_eshell_lt_top [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] (r : ℕ) : ν (eshell K L v w r) < ⊤ :=
  lt_of_le_of_lt (measure_mono (eshell_subset_shell K L v w r)) (measure_shell_lt_top K L v w ν r)

open scoped TensorProduct.RightActions in

theorem measureReal_eshell_succ [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] (r : ℕ) :
    ν.real (eshell K L v w (r + 1)) =
      (ν.real (shell K L v w 0)) *
        ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (r + 1) - (Ideal.absNorm w.1.asIdeal : ℝ) ^ r) := by
  rw [measureReal_def, eshell_succ, measure_diff (shell_mono_nat K L v w r) (measurableSet_shell K L v w r).nullMeasurableSet
    (measure_shell_lt_top K L v w ν r).ne, ENNReal.toReal_sub_of_le (measure_mono (shell_mono_nat K L v w r))
    (measure_shell_lt_top K L v w ν _).ne, measure_shell, measure_shell, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_natCast, measureReal_def]
  ring

end SemiLocal

section Trace

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "𝒪v" => v.adicCompletionIntegers K

theorem trace_left_tmul (t : Kv) (b : L) :
    Algebra.trace Kv (Kv ⊗[K] L) (t ⊗ₜ[K] b) = t * algebraMap K Kv (Algebra.trace K L b) := by
  have h1 : (t ⊗ₜ[K] b : Kv ⊗[K] L) = t • ((1 : Kv) ⊗ₜ[K] b) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : Algebra.lmul Kv (Kv ⊗[K] L) ((1 : Kv) ⊗ₜ[K] b) = (Algebra.lmul K L b).baseChange Kv := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext b'
    simp
  rw [h1, map_smul, smul_eq_mul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, Algebra.trace_apply]

open scoped TensorProduct.RightActions in

theorem trace_tmul (b : L) (t : Kv) :
    Algebra.trace Kv (L ⊗[K] Kv) (b ⊗ₜ[K] t) = t * algebraMap K Kv (Algebra.trace K L b) := by
  have h : (TensorProduct.RightActions.Algebra.TensorProduct.comm K Kv L) (t ⊗ₜ[K] b) = b ⊗ₜ[K] t := by
    simp
  rw [← h, Algebra.trace_eq_of_algEquiv, trace_left_tmul]

omit [NumberField L] in
open scoped TensorProduct.RightActions in

theorem trace_one_tmul_mul (s : Kv) (x : L ⊗[K] Kv) :
    Algebra.trace Kv (L ⊗[K] Kv) ((1 ⊗ₜ[K] s) * x) = s * Algebra.trace Kv (L ⊗[K] Kv) x := by
  have : (1 ⊗ₜ[K] s) * x = s • x := (Algebra.smul_def s x).symm
  rw [this, map_smul, smul_eq_mul]

open scoped TensorProduct.RightActions in

theorem E_one_tmul_mul (s : Kv) (x : L ⊗[K] Kv) (w' : v.Extension (𝓞 L)) :
    E K L v ((1 ⊗ₜ[K] s) * x) w' = algebraMap Kv (w'.1.adicCompletion L) s * E K L v x w' := by
  rw [map_mul, Pi.mul_apply]
  congr 1
  show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v (1 ⊗ₜ[K] s) w' = _
  rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]

open scoped TensorProduct.RightActions in

theorem E_tmul (b : L) (s : Kv) (w' : v.Extension (𝓞 L)) :
    E K L v (b ⊗ₜ[K] s) w' = algebraMap L (w'.1.adicCompletion L) b * algebraMap Kv (w'.1.adicCompletion L) s := by
  show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v (b ⊗ₜ[K] s) w' = _
  rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply]

theorem valued_algebraMap_eq (w' : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1) (s : Kv) :
    Valued.v (algebraMap Kv (w'.1.adicCompletion L) s) = Valued.v s := by
  rw [show algebraMap Kv (w'.1.adicCompletion L) s = w'.adicCompletionSemialgHom K L s from rfl,
    IsDedekindDomain.HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w' s, hunr w'.1 w'.2, pow_one]

theorem valued_algebraMap_trace_coe (y : 𝓞 L) :
    Valued.v (algebraMap K Kv (Algebra.trace K L (y : L))) =
      v.intValuation (Algebra.intTrace (𝓞 K) (𝓞 L) y) := by
  have h : Algebra.trace K L (y : L) = algebraMap (𝓞 K) K (Algebra.intTrace (𝓞 K) (𝓞 L) y) :=
    (Algebra.algebraMap_intTrace (A := 𝓞 K) (K := K) (L := L) (B := 𝓞 L) y).symm
  rw [h, ← HeightOneSpectrum.valuation_of_algebraMap (K := K) v]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem valued_algebraMap_trace_coe_le_one (y : 𝓞 L) :
    Valued.v (algebraMap K Kv (Algebra.trace K L (y : L))) ≤ 1 := by
  rw [valued_algebraMap_trace_coe]
  exact HeightOneSpectrum.intValuation_le_one v _

open scoped TensorProduct.RightActions in

theorem valued_trace_le_one_of_mem_shell_zero (w : v.Extension (𝓞 L)) {x : L ⊗[K] Kv} (hx : x ∈ shell K L v w 0) :
    Valued.v (Algebra.trace Kv (L ⊗[K] Kv) x) ≤ 1 := by
  rw [shell_zero_eq] at hx
  obtain ⟨z, rfl⟩ := hx
  rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul b t =>
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, trace_tmul]
    refine mul_mem t.2 ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact valued_algebraMap_trace_coe_le_one K L v b
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

open scoped TensorProduct.RightActions in

theorem continuous_trace : Continuous (Algebra.trace Kv (L ⊗[K] Kv)) :=
  IsModuleTopology.continuous_of_linearMap _

open scoped TensorProduct.RightActions in

theorem one_tmul_mul_mem_shell_zero (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    {n : ℕ} {c : Kv} (hc : Valued.v c = WithZero.exp (-(n : ℤ))) {x : L ⊗[K] Kv} (hx : x ∈ shell K L v w n) :
    (1 ⊗ₜ[K] c) * x ∈ shell K L v w 0 := by
  rw [mem_shell_iff] at hx ⊢
  refine ⟨fun w' hw' => ?_, ?_⟩
  · rw [E_one_tmul_mul, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, valued_algebraMap_eq K L v w' hunr, hc]
    calc WithZero.exp (-(n : ℤ)) * Valued.v (E K L v x w')
        ≤ 1 * 1 := mul_le_mul' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
          ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx.1 w' hw'))
      _ = WithZero.exp 0 := by rw [mul_one, WithZero.exp_zero]
  · rw [E_one_tmul_mul, map_mul, valued_algebraMap_eq K L v w hunr, hc]
    calc WithZero.exp (-(n : ℤ)) * Valued.v (E K L v x w)
        ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) := mul_le_mul_right hx.2 _
      _ = WithZero.exp 0 := by rw [← WithZero.exp_add, neg_add_cancel]

open scoped TensorProduct.RightActions in

theorem valued_trace_le_exp (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    (n : ℕ) {x : L ⊗[K] Kv} (hx : x ∈ shell K L v w n) :
    Valued.v (Algebra.trace Kv (L ⊗[K] Kv) x) ≤ WithZero.exp (n : ℤ) := by
  obtain ⟨c, hc, hc0⟩ := exists_valued_eq_exp K v (-(n : ℤ))
  have h := valued_trace_le_one_of_mem_shell_zero K L v w (one_tmul_mul_mem_shell_zero K L v w hunr hc hx)
  rw [trace_one_tmul_mul, map_mul, hc, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_one] at h
  exact h

attribute [local instance] Ideal.Quotient.field in

theorem exists_intTrace_notMem_and_intValuation_le (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1) (n : ℕ) :
    ∃ y : 𝓞 L, Algebra.intTrace (𝓞 K) (𝓞 L) y ∉ v.asIdeal ∧
      ∀ w' : v.Extension (𝓞 L), w' ≠ w → w'.1.intValuation y ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  obtain ⟨w₁, hw₁⟩ := w
  haveI hpm : v.asIdeal.IsMaximal := v.isMaximal
  haveI hPm : w₁.asIdeal.IsMaximal := w₁.isMaximal
  have hunder : (HeightOneSpectrum.under (𝓞 K) w₁).asIdeal = v.asIdeal := by rw [hw₁]
  have hcomap : w₁.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
    rw [← hunder]; rfl
  have hp' : v.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective K L)).not.mpr v.ne_bot
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hp' w₁.asIdeal
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp' w₁.isPrime w₁.ne_bot] at h₂
  have he : v.asIdeal.ramificationIdx' w₁.asIdeal = 1 := by
    have := hunr w₁ hw₁
    rwa [hunder] at this
  rw [he, pow_one] at h₂

  have hQle : ∀ w' : v.Extension (𝓞 L), w' ≠ ⟨w₁, hw₁⟩ → Q ≤ w'.1.asIdeal := by
    intro w' hw'
    have hle : v.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≤ w'.1.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      have hc' : w'.1.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
        obtain ⟨w₂, hw₂⟩ := w'
        show w₂.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal
        rw [← hw₂]; rfl
      rw [hc']
    rw [h₂, Ideal.IsPrime.mul_le w'.1.isPrime] at hle
    rcases hle with hle | hle
    · exfalso
      apply hw'
      have heq : w₁.asIdeal = w'.1.asIdeal := hPm.eq_of_le w'.1.isPrime.ne_top hle
      exact Subtype.ext (HeightOneSpectrum.ext heq).symm
    · exact hle
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
    rw [← Ideal.map_le_iff_le_comap, h₂]
    exact Ideal.mul_le_right)
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w₁.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap (by
    rw [hcomap])
  haveI : w₁.asIdeal.LiesOver v.asIdeal := ⟨by rw [Ideal.under_def, hcomap]⟩
  haveI : IsScalarTower (𝓞 K) (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ Q) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ Q)
  let e : (𝓞 L ⧸ v.asIdeal.map (algebraMap (𝓞 K) (𝓞 L))) ≃ₐ[𝓞 K ⧸ v.asIdeal]
      ((𝓞 L ⧸ w₁.asIdeal) × 𝓞 L ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq h₂).trans
        (Ideal.quotientMulEquivQuotientProd w₁.asIdeal Q (Ideal.isCoprime_iff_sup_eq.mpr h₁)),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have he_snd : ∀ y : 𝓞 L, (e (Ideal.Quotient.mk _ y)).2 = Ideal.Quotient.mk Q y := fun _ => rfl
  obtain ⟨x, hx⟩ : ∃ x, Algebra.trace (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w₁.asIdeal) x ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w₁.asIdeal)
  obtain ⟨y₁, hy₁⟩ := Ideal.Quotient.mk_surjective (e.symm (x, 0))
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (e.symm (1, 0))
  have hzQ : z ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← he_snd, hz, AlgEquiv.apply_symm_apply]
  refine ⟨y₁ * z ^ n, ?_, fun w' hw' => ?_⟩
  · have hy : Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 K) (𝓞 L))) (y₁ * z ^ n) = e.symm (x, 0) := by
      rw [map_mul, map_pow, hy₁, hz, ← map_pow, ← map_mul]
      congr 1
      rw [Prod.pow_mk, Prod.mk_mul_mk, one_pow, mul_one, zero_mul]
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain, hy,
      Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa using hx
  · have hz1 : w'.1.intValuation z ≤ WithZero.exp (-1 : ℤ) :=
      valued_le_exp_neg_one_of_lt_one_int w'.1 ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 (hQle w' hw' hzQ))
    rw [map_mul, map_pow]
    calc w'.1.intValuation y₁ * w'.1.intValuation z ^ n ≤ 1 * WithZero.exp (-1 : ℤ) ^ n :=
          mul_le_mul' (HeightOneSpectrum.intValuation_le_one _ _) (pow_le_pow_left' hz1 n)
      _ = WithZero.exp (-(n : ℤ)) := by rw [one_mul, ← WithZero.exp_nsmul]; simp
where

  valued_le_exp_neg_one_of_lt_one_int (u : HeightOneSpectrum (𝓞 L)) {z : 𝓞 L} (hz : u.intValuation z < 1) :
      u.intValuation z ≤ WithZero.exp (-1 : ℤ) := by
    by_cases h0 : u.intValuation z = 0
    · rw [h0]; exact zero_le'
    · rw [← WithZero.log_le_iff_le_exp h0]
      have h : WithZero.log (u.intValuation z) < 0 := by
        rw [WithZero.log_lt_iff_lt_exp h0, WithZero.exp_zero]; exact hz
      omega

open scoped TensorProduct.RightActions in

theorem exists_mem_shell_trace_eq (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    (n : ℕ) (t : Kv) (ht : Valued.v t ≤ WithZero.exp (n : ℤ)) :
    ∃ x ∈ shell K L v w n, Algebra.trace Kv (L ⊗[K] Kv) x = t := by
  obtain ⟨y, hy, hysmall⟩ := exists_intTrace_notMem_and_intValuation_le K L v w hunr n
  set u : Kv := algebraMap K Kv (Algebra.trace K L (y : L)) with hu
  have hu1 : Valued.v u = 1 := by
    rw [hu, valued_algebraMap_trace_coe]
    exact le_antisymm (HeightOneSpectrum.intValuation_le_one v _)
      (not_lt.1 fun h => hy ((HeightOneSpectrum.intValuation_lt_one_iff_mem v _).1 h))
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  have hs : Valued.v (t * u⁻¹) = Valued.v t := by rw [map_mul, map_inv₀, hu1, inv_one, mul_one]
  refine ⟨(y : L) ⊗ₜ[K] (t * u⁻¹), ?_, ?_⟩
  · rw [mem_shell_iff]
    refine ⟨fun w' hw' => ?_, ?_⟩
    · rw [E_tmul, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, valued_algebraMap_eq K L v w' hunr, hs,
        valued_algebraMap_coe]
      calc w'.1.intValuation y * Valued.v t ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) :=
            mul_le_mul' (hysmall w' hw') ht
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    · rw [E_tmul, map_mul, valued_algebraMap_eq K L v w hunr, hs, valued_algebraMap_coe]
      calc w.1.intValuation y * Valued.v t ≤ 1 * WithZero.exp (n : ℤ) :=
            mul_le_mul' (HeightOneSpectrum.intValuation_le_one _ _) ht
        _ = WithZero.exp (n : ℤ) := one_mul _
  · rw [trace_tmul]
    show t * u⁻¹ * u = t
    rw [mul_assoc, inv_mul_cancel₀ hu0, mul_one]

end Trace

section Levels

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => v.adicCompletion K
local notation "𝒪v" => v.adicCompletionIntegers K

open scoped TensorProduct.RightActions in

def lev (n ℓ : ℤ) : Set (L ⊗[K] Kv) :=
  {x | x ∈ shell K L v w n ∧ Valued.v (Algebra.trace Kv (L ⊗[K] Kv) x) ≤ WithZero.exp ℓ}

open scoped TensorProduct.RightActions in
theorem mem_lev_iff (n ℓ : ℤ) (x : L ⊗[K] Kv) :
    x ∈ lev K L v w n ℓ ↔ x ∈ shell K L v w n ∧ Valued.v (Algebra.trace Kv (L ⊗[K] Kv) x) ≤ WithZero.exp ℓ := Iff.rfl

open scoped TensorProduct.RightActions in
theorem lev_subset (n ℓ : ℤ) : lev K L v w n ℓ ⊆ shell K L v w n := fun _ hx => hx.1

open scoped TensorProduct.RightActions in
theorem lev_eq_inter_preimage (n ℓ : ℤ) :
    lev K L v w n ℓ = shell K L v w n ∩ (Algebra.trace Kv (L ⊗[K] Kv)) ⁻¹' vball K v ℓ := rfl

open scoped TensorProduct.RightActions in
theorem measurableSet_lev [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)] (n ℓ : ℤ) :
    MeasurableSet (lev K L v w n ℓ) := by
  rw [lev_eq_inter_preimage]
  exact (measurableSet_shell K L v w n).inter
    (((isOpen_vball K v _).preimage (continuous_trace K L v)).measurableSet)

open scoped TensorProduct.RightActions in

theorem lev_self (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1) (n : ℕ) :
    lev K L v w n n = shell K L v w n := by
  ext x
  rw [mem_lev_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, valued_trace_le_exp K L v w hunr n h⟩⟩

open scoped TensorProduct.RightActions in
theorem lev_mono_left {m n : ℤ} (h : m ≤ n) (ℓ : ℤ) : lev K L v w m ℓ ⊆ lev K L v w n ℓ := fun _ hx =>
  ⟨shell_mono K L v w h hx.1, hx.2⟩

open scoped TensorProduct.RightActions in

theorem measure_lev_eq_mul_pred
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)]
    (ν : Measure (L ⊗[K] Kv)) [ν.IsAddHaarMeasure] (n : ℕ) (ℓ : ℤ) (hℓ : ℓ ≤ n) :
    ν (lev K L v w n ℓ) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) * ν (lev K L v w n (ℓ - 1)) := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L Kv
  set T := Algebra.trace Kv (L ⊗[K] Kv) with hT

  haveI : Finite (IsLocalRing.ResidueField 𝒪v) := inferInstance
  letI : Fintype (IsLocalRing.ResidueField 𝒪v) := Fintype.ofFinite _
  have hsurj : Function.Surjective (IsLocalRing.residue 𝒪v) := IsLocalRing.residue_surjective
  set s : IsLocalRing.ResidueField 𝒪v → 𝒪v := Function.surjInv hsurj with hs
  have hs_mk : ∀ ρ, IsLocalRing.residue 𝒪v (s ρ) = ρ := fun ρ => Function.surjInv_eq hsurj ρ

  obtain ⟨c, hcv, hc0⟩ := exists_valued_eq_exp K v ℓ
  have hcinv : Valued.v c⁻¹ = WithZero.exp (-ℓ) := by
    rw [map_inv₀, hcv, WithZero.exp_neg]
  have hexp : WithZero.exp ℓ * WithZero.exp (-1 : ℤ) = WithZero.exp (ℓ - 1) := by
    rw [← WithZero.exp_add]; congr 1

  have hcs : ∀ ρ, Valued.v (c * (s ρ : Kv)) ≤ WithZero.exp ℓ := by
    intro ρ
    rw [map_mul, hcv]
    calc WithZero.exp ℓ * Valued.v (s ρ : Kv) ≤ WithZero.exp ℓ * 1 := mul_le_mul_right (s ρ).2 _
      _ = WithZero.exp ℓ := mul_one _
  have hcsn : ∀ ρ, Valued.v (c * (s ρ : Kv)) ≤ WithZero.exp (n : ℤ) := fun ρ =>
    (hcs ρ).trans (WithZero.exp_le_exp.2 hℓ)
  choose xc hxcO hxcT using fun ρ => exists_mem_shell_trace_eq K L v w hunr n (c * (s ρ : Kv)) (hcsn ρ)

  set piece : IsLocalRing.ResidueField 𝒪v → Set (L ⊗[K] Kv) := fun ρ =>
    (fun x => -xc ρ + x) ⁻¹' lev K L v w n (ℓ - 1) with hpiece
  have hmem_piece : ∀ ρ x, x ∈ piece ρ ↔
      x - xc ρ ∈ shell K L v w n ∧ Valued.v (T x - c * (s ρ : Kv)) ≤ WithZero.exp (ℓ - 1) := by
    intro ρ x
    simp only [hpiece, Set.mem_preimage]
    rw [mem_lev_iff, ← hT, map_add, map_neg, hxcT, neg_add_eq_sub, neg_add_eq_sub]

  have hcover : (⋃ ρ, piece ρ) = lev K L v w n ℓ := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨ρ, hρ⟩
      rw [hmem_piece] at hρ
      have hxO : x ∈ shell K L v w n := by
        have := add_mem_shell K L v w hρ.1 (hxcO ρ)
        rwa [sub_add_cancel] at this
      refine ⟨hxO, ?_⟩
      have hsplit : T x = (T x - c * (s ρ : Kv)) + c * (s ρ : Kv) := by ring
      rw [← hT, hsplit]
      refine (Valuation.map_add _ _ _).trans (max_le (hρ.2.trans ?_) (hcs ρ))
      rw [WithZero.exp_le_exp]; linarith
    · intro hx
      rw [mem_lev_iff, ← hT] at hx

      have ht : c⁻¹ * T x ∈ 𝒪v := by
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hcinv]
        calc WithZero.exp (-ℓ) * Valued.v (T x) ≤ WithZero.exp (-ℓ) * WithZero.exp ℓ :=
              mul_le_mul_right hx.2 _
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      set t : 𝒪v := ⟨c⁻¹ * T x, ht⟩ with ht'
      refine ⟨IsLocalRing.residue 𝒪v t, ?_⟩
      rw [hmem_piece]
      refine ⟨sub_mem_shell K L v w hx.1 (hxcO _), ?_⟩
      have hkey : T x - c * (s (IsLocalRing.residue 𝒪v t) : Kv) =
          c * ((t : Kv) - (s (IsLocalRing.residue 𝒪v t) : Kv)) := by
        rw [ht']; push_cast; field_simp
      rw [hkey, map_mul, hcv, ← hexp]
      refine mul_le_mul_right (valued_le_exp_neg_one_of_lt_one K v ?_) _
      exact (residue_eq_residue_iff K v t (s (IsLocalRing.residue 𝒪v t))).1 (hs_mk _).symm

  have hdisj : Pairwise (Function.onFun Disjoint piece) := by
    intro ρ ρ' hρρ'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [hmem_piece] at hx hx'
    apply hρρ'
    rw [← hs_mk ρ, ← hs_mk ρ', residue_eq_residue_iff]
    have hd : Valued.v (c * ((s ρ : Kv) - (s ρ' : Kv))) ≤ WithZero.exp (ℓ - 1) := by
      have : c * ((s ρ : Kv) - (s ρ' : Kv)) = (T x - c * (s ρ' : Kv)) + -(T x - c * (s ρ : Kv)) := by ring
      rw [this]
      refine (Valuation.map_add _ _ _).trans (max_le hx'.2 ?_)
      rw [Valuation.map_neg]; exact hx.2
    have hd' : Valued.v ((s ρ : Kv) - (s ρ' : Kv)) ≤ WithZero.exp (-1 : ℤ) := by
      have : (s ρ : Kv) - (s ρ' : Kv) = c⁻¹ * (c * ((s ρ : Kv) - (s ρ' : Kv))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      rw [this, map_mul, hcinv]
      calc WithZero.exp (-ℓ) * Valued.v (c * ((s ρ : Kv) - (s ρ' : Kv)))
          ≤ WithZero.exp (-ℓ) * WithZero.exp (ℓ - 1) := mul_le_mul_right hd _
        _ = WithZero.exp (-1 : ℤ) := by rw [← WithZero.exp_add]; congr 1; ring
    calc Valued.v ((s ρ : Kv) - (s ρ' : Kv)) ≤ WithZero.exp (-1 : ℤ) := hd'
      _ < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hmeas : ∀ ρ, MeasurableSet (piece ρ) := fun ρ =>
    (measurable_const_add _) (measurableSet_lev K L v w n (ℓ - 1))
  have hμ : ∀ ρ, ν (piece ρ) = ν (lev K L v w n (ℓ - 1)) := fun ρ => measure_preimage_add ν _ _
  rw [← hcover, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, natCard_residueField K v]

open scoped TensorProduct.RightActions in

theorem measure_lev
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)]
    (ν : Measure (L ⊗[K] Kv)) [ν.IsAddHaarMeasure] (n k : ℕ) :
    ν (lev K L v w n ((n : ℤ) - k)) = ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹) ^ k * ν (shell K L v w n) := by
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (one_lt_absNorm K v)).ne'
  have hqt : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  induction k with
  | zero => rw [pow_zero, one_mul, Nat.cast_zero, sub_zero, lev_self K L v w hunr]
  | succ k ih =>
    have h := measure_lev_eq_mul_pred K L v w hunr ν n ((n : ℤ) - k) (by linarith)
    rw [ih] at h
    have hcast : (n : ℤ) - ((k + 1 : ℕ) : ℤ) = (n : ℤ) - k - 1 := by push_cast; ring
    rw [hcast]
    calc ν (lev K L v w n ((n : ℤ) - k - 1))
        = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ *
            ((Ideal.absNorm v.asIdeal : ℝ≥0∞) * ν (lev K L v w n ((n : ℤ) - k - 1))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 hqt, one_mul]
      _ = ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹) ^ (k + 1) * ν (shell K L v w n) := by
          rw [← h, pow_succ]; ring

end Levels

section Analysis

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => v.adicCompletion K
local notation "𝒪v" => v.adicCompletionIntegers K

open scoped TensorProduct.RightActions in

private def _root_.KcLogShellTrace.sub (n : ℕ) (S : Set (L ⊗[K] Kv)) (k : ℕ) : Set (L ⊗[K] Kv) :=
  S ∩ {x | Valued.v (Algebra.trace Kv (L ⊗[K] Kv) x) ≤ WithZero.exp ((n : ℤ) - (k + 1 : ℕ))}

p2m_export "KcLogShellTrace" "sub"
omit [NumberField L] in
open scoped TensorProduct.RightActions in
theorem mem_sub_iff (n : ℕ) (S : Set (L ⊗[K] Kv)) (k : ℕ) (x : L ⊗[K] Kv) :
    x ∈ sub K L v n S k ↔ x ∈ S ∧ Valued.v (Algebra.trace Kv (L ⊗[K] Kv) x) ≤ WithZero.exp ((n : ℤ) - (k + 1 : ℕ)) :=
  Iff.rfl

open scoped TensorProduct.RightActions in
theorem measurableSet_sub [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)] (n : ℕ) {S : Set (L ⊗[K] Kv)}
    (hS : MeasurableSet S) (k : ℕ) : MeasurableSet (sub K L v n S k) :=
  hS.inter (((isOpen_vball K v _).preimage (continuous_trace K L v)).measurableSet)

open scoped TensorProduct.RightActions in

def A (n : ℕ) (S : Set (L ⊗[K] Kv)) (x : L ⊗[K] Kv) : ℝ≥0∞ :=
  ∑' k : ℕ, (sub K L v n S k).indicator (fun _ => (1 : ℝ≥0∞)) x

open scoped TensorProduct.RightActions in
theorem measurable_A [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)] (n : ℕ) {S : Set (L ⊗[K] Kv)}
    (hS : MeasurableSet S) : Measurable (A K L v n S) :=
  Measurable.tsum fun k => measurable_const.indicator (measurableSet_sub K L v n hS k)

theorem tsum_ite_succ_le_eq (N : ℕ) :
    (∑' m : ℕ, (if m + 1 ≤ N then (1 : ℝ≥0∞) else 0)) = N := by
  rw [tsum_eq_sum (s := Finset.range N)]
  · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    rw [Finset.filter_true_of_mem fun m hm => by rw [Finset.mem_range] at hm; omega]
    exact Finset.card_range N
  · intro m hm
    rw [Finset.mem_range] at hm
    rw [if_neg (by omega)]

open scoped TensorProduct.RightActions in

theorem log_valued_trace_eq (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    (n : ℕ) {S : Set (L ⊗[K] Kv)} (hS : S ⊆ shell K L v w n) {x : L ⊗[K] Kv} (hx : x ∈ S)
    (hA : A K L v n S x ≠ ⊤) :
    ((WithZero.log (Valued.v (Algebra.trace Kv (L ⊗[K] Kv) x)) : ℤ) : ℝ) = (n : ℝ) - (A K L v n S x).toReal := by
  set y := Algebra.trace Kv (L ⊗[K] Kv) x with hy
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hA
    unfold A
    have : ∀ k : ℕ, (sub K L v n S k).indicator (fun _ => (1 : ℝ≥0∞)) x = 1 := by
      intro k
      rw [Set.indicator_of_mem]
      rw [mem_sub_iff, ← hy, hy0, map_zero]
      exact ⟨hx, zero_le'⟩
    simp_rw [this]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  set ℓ : ℤ := WithZero.log (Valued.v y) with hℓ
  have hℓn : ℓ ≤ n := by
    rw [hℓ, WithZero.log_le_iff_le_exp hv0]
    exact valued_trace_le_exp K L v w hunr n (hS hx)
  set N : ℕ := ((n : ℤ) - ℓ).toNat with hN
  have hNℓ : (N : ℤ) = n - ℓ := by rw [hN]; omega
  have hAN : A K L v n S x = N := by
    unfold A
    rw [← tsum_ite_succ_le_eq]
    refine tsum_congr fun k => ?_
    by_cases hk : k + 1 ≤ N
    · rw [if_pos hk, Set.indicator_of_mem]
      rw [mem_sub_iff, ← hy]
      refine ⟨hx, ?_⟩
      rw [← WithZero.log_le_iff_le_exp hv0, ← hℓ]
      push_cast; omega
    · rw [if_neg hk, Set.indicator_of_notMem]
      rw [mem_sub_iff, ← hy, not_and]
      intro _ hle
      rw [← WithZero.log_le_iff_le_exp hv0, ← hℓ] at hle
      push_cast at hle; omega
  rw [hAN, ENNReal.toReal_natCast]
  have : (ℓ : ℝ) = (n : ℝ) - (N : ℝ) := by exact_mod_cast (show ℓ = (n : ℤ) - N by omega)
  exact this

open scoped TensorProduct.RightActions in

theorem lintegral_A [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)]
    (ν : Measure (L ⊗[K] Kv)) (n : ℕ) {S : Set (L ⊗[K] Kv)} (hS : MeasurableSet S) :
    ∫⁻ x in S, A K L v n S x ∂ν = ∑' k : ℕ, ν (sub K L v n S k) := by
  unfold A
  rw [lintegral_tsum fun k => (measurable_const.indicator (measurableSet_sub K L v n hS k)).aemeasurable]
  refine tsum_congr fun k => ?_
  rw [show (fun _ => (1 : ℝ≥0∞)) = (1 : L ⊗[K] Kv → ℝ≥0∞) from rfl,
    lintegral_indicator_one (measurableSet_sub K L v n hS k), Measure.restrict_apply (measurableSet_sub K L v n hS k),
    Set.inter_eq_left.2 (fun x hx => ((mem_sub_iff K L v n S k x).1 hx).1)]

theorem tsum_inv_pow (q : ℕ) (hq : 1 < q) :
    (∑' k : ℕ, ((q : ℝ≥0∞)⁻¹) ^ k) ≠ ⊤ ∧
    (∑' k : ℕ, ((q : ℝ≥0∞)⁻¹) ^ k).toReal = (q : ℝ) / ((q : ℝ) - 1) := by
  have hlt : (q : ℝ≥0∞)⁻¹ < 1 := by
    rw [ENNReal.inv_lt_one]; exact_mod_cast hq
  have hne : (1 - (q : ℝ≥0∞)⁻¹) ≠ 0 := (tsub_pos_of_lt hlt).ne'
  rw [ENNReal.tsum_geometric]
  refine ⟨ENNReal.inv_ne_top.2 hne, ?_⟩
  rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hlt.le ENNReal.one_ne_top, ENNReal.toReal_inv, ENNReal.toReal_one,
    ENNReal.toReal_natCast]
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

open scoped TensorProduct.RightActions in

theorem integrableOn_and_setIntegral_of_masses
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)]
    (ν : Measure (L ⊗[K] Kv)) (n : ℕ) {S : Set (L ⊗[K] Kv)} (hSm : MeasurableSet S)
    (hS : S ⊆ shell K L v w n) (hSf : ν S ≠ ⊤) (D : ℝ≥0∞) (hD : D ≠ ⊤)
    (hmass : ∀ k : ℕ, ν (sub K L v n S k) = D * ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹) ^ k) :
    IntegrableOn (fun x : L ⊗[K] Kv => ((Real.log (LanglandsTunnell.TateLocal.modulus
        (Algebra.trace Kv (L ⊗[K] Kv) x) : ℝ) : ℝ) : ℂ)) S ν ∧
    ∫ x in S, (fun x : L ⊗[K] Kv => ((Real.log (LanglandsTunnell.TateLocal.modulus
        (Algebra.trace Kv (L ⊗[K] Kv) x) : ℝ) : ℝ) : ℂ)) x ∂ν =
      ((Real.log (Ideal.absNorm v.asIdeal : ℝ) *
          ((n : ℝ) * ν.real S - D.toReal * ((Ideal.absNorm v.asIdeal : ℝ) / ((Ideal.absNorm v.asIdeal : ℝ) - 1))) : ℝ) : ℂ) := by
  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  have hq1 : 1 < q := one_lt_absNorm K v
  haveI : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.2 hSf

  have hlin : ∫⁻ x in S, A K L v n S x ∂ν = D * ∑' k : ℕ, ((q : ℝ≥0∞)⁻¹) ^ k := by
    rw [lintegral_A K L v ν n hSm]
    simp_rw [hmass]
    rw [ENNReal.tsum_mul_left]
  have hlin_ne : ∫⁻ x in S, A K L v n S x ∂ν ≠ ⊤ := by
    rw [hlin]; exact ENNReal.mul_ne_top hD (tsum_inv_pow q hq1).1
  have hlin_real : (∫⁻ x in S, A K L v n S x ∂ν).toReal = D.toReal * ((q : ℝ) / ((q : ℝ) - 1)) := by
    rw [hlin, ENNReal.toReal_mul, (tsum_inv_pow q hq1).2]

  set f : L ⊗[K] Kv → ℂ := fun x => ((Real.log (LanglandsTunnell.TateLocal.modulus
        (Algebra.trace Kv (L ⊗[K] Kv) x) : ℝ) : ℝ) : ℂ) with hf
  set g : L ⊗[K] Kv → ℂ := fun x =>
    ((Real.log (q : ℝ) * ((n : ℝ) - (A K L v n S x).toReal) : ℝ) : ℂ) with hg
  have hae : f =ᵐ[ν.restrict S] g := by
    have h1 : ∀ᵐ x ∂(ν.restrict S), A K L v n S x < ⊤ :=
      ae_lt_top' (measurable_A K L v n hSm).aemeasurable hlin_ne
    have h2 : ∀ᵐ x ∂(ν.restrict S), x ∈ S := ae_restrict_mem hSm
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [hf, hg]
    rw [log_modulus_eq K v, log_valued_trace_eq K L v w hunr n hS hx2 hx1.ne, mul_comm]

  have hAint : Integrable (fun x => (A K L v n S x).toReal) (ν.restrict S) :=
    integrable_toReal_of_lintegral_ne_top (measurable_A K L v n hSm).aemeasurable hlin_ne
  have hgint : Integrable g (ν.restrict S) := by
    have h : Integrable (fun x => Real.log (q : ℝ) * ((n : ℝ) - (A K L v n S x).toReal)) (ν.restrict S) :=
      ((integrable_const (n : ℝ)).sub hAint).const_mul _
    exact h.ofReal
  refine ⟨Integrable.congr hgint hae.symm, ?_⟩
  rw [integral_congr_ae hae]
  simp only [hg]
  rw [integral_complex_ofReal, integral_const_mul, integral_sub (integrable_const _) hAint, integral_const,
    integral_toReal (measurable_A K L v n hSm).aemeasurable
      (ae_lt_top' (measurable_A K L v n hSm).aemeasurable hlin_ne), hlin_real, smul_eq_mul,
    measureReal_restrict_apply_univ]
  push_cast
  ring

end Analysis

section Assembly

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => v.adicCompletion K

open scoped TensorProduct.RightActions in

def f (x : L ⊗[K] Kv) : ℂ :=
  ((Real.log (LanglandsTunnell.TateLocal.modulus (Algebra.trace Kv (L ⊗[K] Kv) x) : ℝ) : ℝ) : ℂ)

open scoped TensorProduct.RightActions in

theorem moment_zero (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)]
    (ν : Measure (L ⊗[K] Kv)) [ν.IsAddHaarMeasure] :
    IntegrableOn (f K L v) (eshell K L v w 0) ν ∧
    ∫ x in eshell K L v w 0, f K L v x ∂ν =
      ((Real.log (Ideal.absNorm v.asIdeal : ℝ) *
        (-(ν.real (shell K L v w 0)) / ((Ideal.absNorm v.asIdeal : ℝ) - 1)) : ℝ) : ℂ) := by
  have hq1 : 1 < Ideal.absNorm v.asIdeal := one_lt_absNorm K v
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'
  have hDt : (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ * ν (shell K L v w 0) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hq0) (measure_shell_zero_lt_top K L v w ν).ne
  have hmass : ∀ k : ℕ, ν (sub K L v 0 (eshell K L v w 0) k) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ * ν (shell K L v w 0)) * ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    have hset : sub K L v 0 (eshell K L v w 0) k = lev K L v w ((0 : ℕ) : ℤ) (((0 : ℕ) : ℤ) - (k + 1 : ℕ)) := by
      ext x
      rw [mem_sub_iff, mem_lev_iff, eshell_zero, Nat.cast_zero]
    rw [hset, measure_lev K L v w hunr ν 0 (k + 1), Nat.cast_zero, pow_succ]
    ring
  have h := integrableOn_and_setIntegral_of_masses K L v w hunr ν 0 (measurableSet_eshell K L v w 0)
    (eshell_subset_shell K L v w 0) (measure_eshell_lt_top K L v w ν 0).ne _ hDt hmass
  refine ⟨h.1, ?_⟩
  rw [show (fun x => f K L v x) = f K L v from rfl]
  unfold f
  rw [h.2, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← measureReal_def, eshell_zero]
  congr 1
  have hq1' : (1 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast hq1
  have : (Ideal.absNorm v.asIdeal : ℝ) - 1 ≠ 0 := by linarith
  have : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

open scoped TensorProduct.RightActions in

theorem moment_succ (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)]
    (ν : Measure (L ⊗[K] Kv)) [ν.IsAddHaarMeasure] (r : ℕ) :
    IntegrableOn (f K L v) (eshell K L v w (r + 1)) ν ∧
    ∫ x in eshell K L v w (r + 1), f K L v x ∂ν =
      ((Real.log (Ideal.absNorm v.asIdeal : ℝ) *
        (((r + 1 : ℕ) : ℝ) * (ν.real (shell K L v w 0) *
            ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (r + 1) - (Ideal.absNorm w.1.asIdeal : ℝ) ^ r)) -
          (((Ideal.absNorm v.asIdeal : ℝ)⁻¹ * (Ideal.absNorm w.1.asIdeal : ℝ) ^ (r + 1) -
              (Ideal.absNorm w.1.asIdeal : ℝ) ^ r) * ν.real (shell K L v w 0)) *
            ((Ideal.absNorm v.asIdeal : ℝ) / ((Ideal.absNorm v.asIdeal : ℝ) - 1))) : ℝ) : ℂ) := by
  have hq1 : 1 < Ideal.absNorm v.asIdeal := one_lt_absNorm K v
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'

  set a : ℝ≥0∞ := (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ * ν (shell K L v w (r + 1 : ℕ)) with ha
  set b : ℝ≥0∞ := ν (shell K L v w r) with hb
  have hat : a ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hq0) (measure_shell_lt_top K L v w ν _).ne
  have hbt : b ≠ ⊤ := (measure_shell_lt_top K L v w ν r).ne
  have hlevA : ∀ k : ℕ, ν (lev K L v w (r + 1 : ℕ) ((r : ℤ) - k)) = a * ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    have h := measure_lev K L v w hunr ν (r + 1) (k + 1)
    have hcast : ((r + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) = (r : ℤ) - k := by push_cast; ring
    rw [hcast] at h
    rw [h, ha, pow_succ]; ring
  have hlevB : ∀ k : ℕ, ν (lev K L v w r ((r : ℤ) - k)) = b * ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    rw [measure_lev K L v w hunr ν r k, hb, mul_comm]
  have hsubset : ∀ k : ℕ, lev K L v w r ((r : ℤ) - k) ⊆ lev K L v w (r + 1 : ℕ) ((r : ℤ) - k) := fun k =>
    lev_mono_left K L v w (by push_cast; linarith) _
  have hba : b ≤ a := by
    have h := measure_mono (μ := ν) (hsubset 0)
    rw [hlevA 0, hlevB 0, pow_zero, mul_one, mul_one] at h
    exact h
  set D : ℝ≥0∞ := a - b with hD
  have hDt : D ≠ ⊤ := ENNReal.sub_ne_top hat
  have hmass : ∀ k : ℕ, ν (sub K L v (r + 1) (eshell K L v w (r + 1)) k) = D * ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    have hset : sub K L v (r + 1) (eshell K L v w (r + 1)) k =
        lev K L v w (r + 1 : ℕ) ((r : ℤ) - k) \ lev K L v w r ((r : ℤ) - k) := by
      ext x
      rw [mem_sub_iff, eshell_succ, Set.mem_diff, Set.mem_diff, mem_lev_iff, mem_lev_iff]
      have hcast : ((r + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) = (r : ℤ) - k := by push_cast; ring
      rw [hcast]
      tauto
    rw [hset, measure_diff (hsubset k) (measurableSet_lev K L v w _ _).nullMeasurableSet
      (by rw [hlevB]; exact ENNReal.mul_ne_top hbt (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hq0))),
      hlevA, hlevB, hD, ENNReal.sub_mul fun _ _ => ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hq0)]
  have h := integrableOn_and_setIntegral_of_masses K L v w hunr ν (r + 1) (measurableSet_eshell K L v w (r + 1))
    (eshell_subset_shell K L v w (r + 1)) (measure_eshell_lt_top K L v w ν (r + 1)).ne D hDt hmass
  refine ⟨h.1, ?_⟩
  rw [show (fun x => f K L v x) = f K L v from rfl]
  unfold f
  rw [h.2, hD, ENNReal.toReal_sub_of_le hba hat, ha, hb, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    measure_shell K L v w ν (r + 1), measure_shell K L v w ν r, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ← measureReal_def, measureReal_eshell_succ]
  have hq1' : (1 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast hq1
  have : (Ideal.absNorm v.asIdeal : ℝ) - 1 ≠ 0 := by linarith
  have : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

open scoped TensorProduct.RightActions in

theorem integrand_eq_sum (h : ℕ → ℂ) (R : ℕ) (hR : ∀ r, R < r → h r = 0) (x : L ⊗[K] Kv) :
    {x : L ⊗[K] Kv | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
        E K L v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
      (fun x => h (poleOrder K L v w (E K L v x w))) x * f K L v x =
    ∑ r ∈ Finset.range (R + 1), (eshell K L v w r).indicator (fun x => h r * f K L v x) x := by
  classical
  by_cases hA : ∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L
  · rw [Set.indicator_of_mem (by exact hA)]
    have hind : ∀ r, (eshell K L v w r).indicator (fun x => h r * f K L v x) x =
        if poleOrder K L v w (E K L v x w) = r then h r * f K L v x else 0 := by
      intro r
      by_cases hr : poleOrder K L v w (E K L v x w) = r
      · rw [if_pos hr, Set.indicator_of_mem (show x ∈ eshell K L v w r from ⟨hA, hr⟩)]
      · rw [if_neg hr, Set.indicator_of_notMem]
        exact fun hx => hr hx.2
    simp only [hind, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hlt
    · rfl
    · rw [hR _ (by omega), zero_mul]
  · rw [Set.indicator_of_notMem (by exact hA), zero_mul]
    symm
    refine Finset.sum_eq_zero fun r _ => ?_
    exact Set.indicator_of_notMem (fun hx => hA hx.1) _

theorem sum_range_succ_eq_add_sum_Icc (g : ℕ → ℂ) (R : ℕ) :
    ∑ r ∈ Finset.range (R + 1), g r = g 0 + ∑ r ∈ Finset.Icc 1 R, g r := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ R + 1), add_assoc]

open scoped TensorProduct.RightActions in

theorem piece (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)]
    (ν : Measure (L ⊗[K] Kv)) [ν.IsAddHaarMeasure] (h : ℕ → ℂ) (r : ℕ) :
    Integrable (fun x => (eshell K L v w r).indicator (fun x => h r * f K L v x) x) ν ∧
    ∫ x, (eshell K L v w r).indicator (fun x => h r * f K L v x) x ∂ν = h r * ∫ x in eshell K L v w r, f K L v x ∂ν := by
  have hint : IntegrableOn (f K L v) (eshell K L v w r) ν := by
    cases r with
    | zero => exact (moment_zero K L v w hunr ν).1
    | succ r => exact (moment_succ K L v w hunr ν r).1
  refine ⟨?_, ?_⟩
  · exact (integrable_indicator_iff (measurableSet_eshell K L v w r)).2 (hint.integrable.const_mul (h r))
  · rw [integral_indicator (measurableSet_eshell K L v w r), integral_const_mul]

open scoped TensorProduct.RightActions in

theorem main (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] Kv)] [BorelSpace (L ⊗[K] Kv)]
    (ν : Measure (L ⊗[K] Kv)) [ν.IsAddHaarMeasure] (h : ℕ → ℂ) (R : ℕ) (hR : ∀ r, R < r → h r = 0) :
    Integrable (fun x => {x : L ⊗[K] Kv | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
            E K L v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (poleOrder K L v w (E K L v x w))) x * f K L v x) ν ∧
    ∫ x, {x : L ⊗[K] Kv | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
            E K L v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (poleOrder K L v w (E K L v x w))) x * f K L v x ∂ν =
      ((ν (shell K L v w 0)).toReal : ℂ) *
        ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) *
        (-(h 0) / ((Ideal.absNorm v.asIdeal : ℂ) - 1) +
          ∑ r ∈ Finset.Icc 1 R, h r *
            ((Ideal.absNorm w.1.asIdeal : ℂ) ^ r - (Ideal.absNorm w.1.asIdeal : ℂ) ^ (r - 1)) *
            ((r : ℂ) - 1 / ((Ideal.absNorm v.asIdeal : ℂ) - 1) + 1 / ((Ideal.absNorm w.1.asIdeal : ℂ) - 1))) := by
  have hfun : (fun x => {x : L ⊗[K] Kv | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
            E K L v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (poleOrder K L v w (E K L v x w))) x * f K L v x) =
      fun x => ∑ r ∈ Finset.range (R + 1), (eshell K L v w r).indicator (fun x => h r * f K L v x) x := by
    funext x; exact integrand_eq_sum K L v w h R hR x
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun r _ => (piece K L v w hunr ν h r).1, ?_⟩
  rw [integral_finsetSum _ fun r _ => (piece K L v w hunr ν h r).1]
  simp_rw [(piece K L v w hunr ν h _).2]
  rw [sum_range_succ_eq_add_sum_Icc, (moment_zero K L v w hunr ν).2, ← measureReal_def]
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm K v
  have hN1 : (1 : ℝ) < (Ideal.absNorm w.1.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm L w.1
  have hq1' : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1 ≠ 0 := by
    have h' : ((Ideal.absNorm v.asIdeal : ℝ) - 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast h'
  have hN1' : ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) - 1 ≠ 0 := by
    have h' : ((Ideal.absNorm w.1.asIdeal : ℝ) - 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast h'
  have hq0' : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have h' : ((Ideal.absNorm v.asIdeal : ℝ) : ℝ) ≠ 0 := by linarith
    exact_mod_cast h'
  rw [mul_add, Finset.mul_sum]
  congr 1
  · push_cast
    field_simp
  · refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [(moment_succ K L v w hunr ν r').2, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

end Assembly

end KcLogShellTrace

end

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∀ (h : ℕ → ℂ) (R : ℕ), (∀ r, R < r → h r = 0) →
      Integrable (fun x => {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
            HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (WithZero.log (Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) x * ((Real.log (LanglandsTunnell.TateLocal.modulus (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) : ℝ) : ℝ) : ℂ)) ν ∧
      ∫ x, {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
            HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (WithZero.log (Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) x * ((Real.log (LanglandsTunnell.TateLocal.modulus (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) : ℝ) : ℝ) : ℂ) ∂ν =
      ((ν {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L),
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}).toReal : ℂ) *
        ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) *
        (-(h 0) / ((Ideal.absNorm v.asIdeal : ℂ) - 1) +
          ∑ r ∈ Finset.Icc 1 R, h r *
            ((Ideal.absNorm w.1.asIdeal : ℂ) ^ r - (Ideal.absNorm w.1.asIdeal : ℂ) ^ (r - 1)) *
            ((r : ℂ) - 1 / ((Ideal.absNorm v.asIdeal : ℂ) - 1) + 1 / ((Ideal.absNorm w.1.asIdeal : ℂ) - 1))) := by
  intro h R hR
  rw [KcLogShellTrace.setOf_forall_mem_eq_shell_zero K L v w]
  exact KcLogShellTrace.main K L v w hunr ν h R hR

end S_TwistedUnipotentTerm_integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
end P2MW
export P2MW.S_TwistedUnipotentTerm_integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram (solution)

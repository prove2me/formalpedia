-- Prove2me | solution 1 for TwistedUnipotentTerm.exists_pos_forall_integral_indicator_integralAway_walkShell_eq_mul_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8bc1c01f-0073-59a0-83d7-349edf015071

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_exists_pos_forall_integral_indicator_integralAway_walkShell_eq_mul_add_sum

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace KcWalkShellIntegral

section LocalField

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

local notation "Fu" => u.adicCompletion F
local notation "𝒪u" => u.adicCompletionIntegers F

theorem exists_valued_eq_exp_neg_one : ∃ π : Fu, Valued.v π = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer F u
  refine ⟨algebraMap F Fu π, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]

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

theorem vball_zero : vball F u 0 = (𝒪u : Set Fu) := by
  ext y
  rw [mem_vball_iff, WithZero.exp_zero, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

theorem vball_eq_preimage {c : Fu} {n : ℤ} (hc : Valued.v c = WithZero.exp (-n)) :
    vball F u n = (fun y => c * y) ⁻¹' (𝒪u : Set Fu) := by
  ext y
  rw [mem_vball_iff, Set.mem_preimage, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    map_mul, hc, WithZero.exp_neg, inv_mul_le_iff₀ (WithZero.exp_pos), mul_one]

theorem isOpen_vball (n : ℤ) : IsOpen (vball F u n) := by
  obtain ⟨π, hπ⟩ := exists_valued_eq_exp_neg_one F u
  have hc : Valued.v (π ^ n) = WithZero.exp (-n) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]; simp
  rw [vball_eq_preimage F u hc]
  exact ((NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 F) F).out u).preimage (continuous_const_mul _)

theorem isCompact_vball (n : ℤ) : IsCompact (vball F u n) := by
  obtain ⟨π, hπ⟩ := exists_valued_eq_exp_neg_one F u
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  have hc : Valued.v (π ^ n) = WithZero.exp (-n) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]; simp
  have hcn0 : π ^ n ≠ 0 := zpow_ne_zero n hπ0
  have hK : IsCompact (𝒪u : Set Fu) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F u)
  have himage : vball F u n = (fun y => (π ^ n)⁻¹ * y) '' (𝒪u : Set Fu) := by
    rw [vball_eq_preimage F u hc]
    ext y
    constructor
    · intro hy
      exact ⟨π ^ n * y, hy, by beta_reduce; rw [← mul_assoc, inv_mul_cancel₀ hcn0, one_mul]⟩
    · rintro ⟨z, hz, rfl⟩
      show π ^ n * ((π ^ n)⁻¹ * z) ∈ (𝒪u : Set Fu)
      rwa [← mul_assoc, mul_inv_cancel₀ hcn0, one_mul]
  rw [himage]
  exact hK.image (continuous_const_mul _)

def poleOrder (y : Fu) : ℕ := (WithZero.log (Valued.v y)).toNat

theorem poleOrder_le_iff (y : Fu) (n : ℕ) : poleOrder F u y ≤ n ↔ y ∈ vball F u n := by
  rw [poleOrder, mem_vball_iff, Int.toNat_le]
  by_cases hy : y = 0
  · subst hy
    simp
  · have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    rw [WithZero.log_le_iff_le_exp hv]

theorem valued_le_exp_neg_one_of_lt_one {y : Fu} (hy : Valued.v y < 1) : Valued.v y ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : Valued.v y = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.log_le_iff_le_exp h0]
    have h : WithZero.log (Valued.v y) < 0 := by
      rw [WithZero.log_lt_iff_lt_exp h0, WithZero.exp_zero]; exact hy
    omega

theorem isClosed_integers : IsClosed (𝒪u : Set Fu) :=
  (isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F u)).isClosed

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

open scoped TensorProduct.RightActions in
theorem isCompact_shell_zero : IsCompact (shell K L v w 0) := by
  rw [shell_zero_eq]; exact AutomorphicForm.isCompact_semiLocalIntegers K L v

open scoped TensorProduct.RightActions in
theorem zero_mem_shell (n : ℕ) : (0 : L ⊗[K] v.adicCompletion K) ∈ shell K L v w n := by
  rw [mem_shell_iff]
  simp only [map_zero, Pi.zero_apply, zero_mem, implies_true, true_and]
  exact zero_le'

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

theorem E_sub_tvec_self (x : L ⊗[K] v.adicCompletion K) (c : w.1.adicCompletion L) :
    E K L v (x - tvec K L v w c) w = E K L v x w - c := by
  rw [map_sub, Pi.sub_apply, E_tvec_self]

theorem E_sub_tvec_of_ne (x : L ⊗[K] v.adicCompletion K) (c : w.1.adicCompletion L) {w' : v.Extension (𝓞 L)}
    (hw' : w' ≠ w) : E K L v (x - tvec K L v w c) w' = E K L v x w' := by
  rw [map_sub, Pi.sub_apply, E_tvec_of_ne K L v w c hw', sub_zero]

theorem sub_tvec_mem_shell_iff (n : ℤ) (x : L ⊗[K] v.adicCompletion K) (c : w.1.adicCompletion L) :
    x - tvec K L v w c ∈ shell K L v w n ↔
      (∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L) ∧
        Valued.v (E K L v x w - c) ≤ WithZero.exp n := by
  rw [mem_shell_iff, E_sub_tvec_self]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' hw' => by rw [← E_sub_tvec_of_ne K L v w x c hw']; exact h1 w' hw', h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' hw' => by rw [E_sub_tvec_of_ne K L v w x c hw']; exact h1 w' hw', h2⟩

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

  obtain ⟨π, hπ⟩ := exists_valued_eq_exp_neg_one L w.1
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  set c : w.1.adicCompletion L := π ^ (n + 1) with hc
  have hcv : Valued.v c = WithZero.exp (-(n + 1 : ℕ) : ℤ) := by
    rw [hc, map_pow, hπ, ← WithZero.exp_nsmul]; simp
  have hc0 : c ≠ 0 := pow_ne_zero _ hπ0
  have hcv0 : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
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

def eshell (r : ℕ) : Set (L ⊗[K] v.adicCompletion K) :=
  {x | (∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L) ∧
    poleOrder L w.1 (E K L v x w) = r}

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
    have : ¬ poleOrder L w.1 (E K L v x w) ≤ r := fun h => h3 ⟨h1, h⟩
    omega

theorem shell_mono (r : ℕ) : shell K L v w r ⊆ shell K L v w (r + 1 : ℕ) := by
  intro x hx
  rw [mem_shell_iff] at hx ⊢
  refine ⟨hx.1, hx.2.trans ?_⟩
  rw [WithZero.exp_le_exp]; push_cast; linarith

open scoped TensorProduct.RightActions in
theorem measurableSet_eshell [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (r : ℕ) : MeasurableSet (eshell K L v w r) := by
  cases r with
  | zero => rw [eshell_zero]; exact measurableSet_shell K L v w 0
  | succ r =>
    rw [eshell_succ]
    exact (measurableSet_shell K L v w _).diff (measurableSet_shell K L v w r)

open scoped TensorProduct.RightActions in
theorem measure_shell_zero_lt_top [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] : ν (shell K L v w 0) < ⊤ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact (isCompact_shell_zero K L v w).measure_lt_top

open scoped TensorProduct.RightActions in
theorem measure_shell_zero_pos [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] : 0 < ν (shell K L v w 0) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact (isOpen_shell K L v w 0).measure_pos ν ⟨0, zero_mem_shell K L v w 0⟩

open scoped TensorProduct.RightActions in
theorem measure_shell_lt_top [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] (r : ℕ) : ν (shell K L v w r) < ⊤ := by
  rw [measure_shell]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.natCast_lt_top _)) (measure_shell_zero_lt_top K L v w ν)

open scoped TensorProduct.RightActions in

theorem measureReal_eshell_succ [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] (r : ℕ) :
    ν.real (eshell K L v w (r + 1)) =
      (ν.real (shell K L v w 0)) *
        ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (r + 1) - (Ideal.absNorm w.1.asIdeal : ℝ) ^ r) := by
  rw [measureReal_def, eshell_succ, measure_diff (shell_mono K L v w r) (measurableSet_shell K L v w r).nullMeasurableSet
    (measure_shell_lt_top K L v w ν r).ne, ENNReal.toReal_sub_of_le (measure_mono (shell_mono K L v w r))
    (measure_shell_lt_top K L v w ν _).ne, measure_shell, measure_shell, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_natCast, measureReal_def]
  ring

open scoped TensorProduct.RightActions in
theorem measureReal_eshell_zero [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ν.real (eshell K L v w 0) = ν.real (shell K L v w 0) := by
  rw [eshell_zero]

theorem integrand_eq_sum (h : ℕ → ℂ) (R : ℕ) (hR : ∀ r, R < r → h r = 0) (x : L ⊗[K] v.adicCompletion K) :
    {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
        E K L v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
      (fun x => h (poleOrder L w.1 (E K L v x w))) x =
    ∑ r ∈ Finset.range (R + 1), (eshell K L v w r).indicator (fun _ => h r) x := by
  classical
  by_cases hA : ∀ w' : v.Extension (𝓞 L), w' ≠ w → E K L v x w' ∈ w'.1.adicCompletionIntegers L
  · rw [Set.indicator_of_mem (by exact hA)]
    have hind : ∀ r, (eshell K L v w r).indicator (fun _ => h r) x =
        if poleOrder L w.1 (E K L v x w) = r then h r else 0 := by
      intro r
      by_cases hr : poleOrder L w.1 (E K L v x w) = r
      · rw [if_pos hr, Set.indicator_of_mem (show x ∈ eshell K L v w r from ⟨hA, hr⟩)]
      · rw [if_neg hr, Set.indicator_of_notMem]
        exact fun hx => hr hx.2
    simp only [hind, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hlt
    · rfl
    · exact hR _ (by omega)
  · rw [Set.indicator_of_notMem (by exact hA)]
    symm
    refine Finset.sum_eq_zero fun r _ => ?_
    exact Set.indicator_of_notMem (fun hx => hA hx.1) _

theorem sum_range_succ_eq_add_sum_Icc (f : ℕ → ℂ) (R : ℕ) :
    ∑ r ∈ Finset.range (R + 1), f r = f 0 + ∑ r ∈ Finset.Icc 1 R, f r := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ R + 1), add_assoc]

open scoped TensorProduct.RightActions in

theorem integral_eq [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] (h : ℕ → ℂ) (R : ℕ) (hR : ∀ r, R < r → h r = 0) :
    ∫ x, {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
        E K L v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
      (fun x => h (poleOrder L w.1 (E K L v x w))) x ∂ν =
    (ν.real (shell K L v w 0) : ℂ) * (h 0 + ∑ r ∈ Finset.Icc 1 R, h r *
      ((Ideal.absNorm w.1.asIdeal : ℂ) ^ r - (Ideal.absNorm w.1.asIdeal : ℂ) ^ (r - 1))) := by
  simp_rw [integrand_eq_sum K L v w h R hR]
  have hint : ∀ r ∈ Finset.range (R + 1), Integrable (fun x => (eshell K L v w r).indicator (fun _ => h r) x) ν := by
    intro r _
    refine (integrable_indicator_iff (measurableSet_eshell K L v w r)).2 (integrableOn_const ?_)
    refine (lt_of_le_of_lt (measure_mono ?_) (measure_shell_lt_top K L v w ν r)).ne
    cases r with
    | zero => rw [eshell_zero]; exact subset_rfl
    | succ r => rw [eshell_succ]; exact Set.diff_subset
  rw [integral_finsetSum _ hint]
  simp_rw [integral_indicator_const _ (measurableSet_eshell K L v w _), Complex.real_smul]
  rw [sum_range_succ_eq_add_sum_Icc, measureReal_eshell_zero, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_Icc] at hr
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [measureReal_eshell_succ, Nat.add_sub_cancel]
  push_cast
  ring

end SemiLocal

end KcWalkShellIntegral

end

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ (h : ℕ → ℂ) (R : ℕ), (∀ r, R < r → h r = 0) →
      ∫ x, {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈
                w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (WithZero.log (Valued.v
            (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) x ∂ν =
        (c : ℂ) * (h 0 + ∑ r ∈ Finset.Icc 1 R, h r *
          ((Ideal.absNorm w.1.asIdeal : ℂ) ^ r - (Ideal.absNorm w.1.asIdeal : ℂ) ^ (r - 1))) := by
  refine ⟨ν.real (KcWalkShellIntegral.shell K L v w 0), ?_, fun h R hR => ?_⟩
  · exact ENNReal.toReal_pos (KcWalkShellIntegral.measure_shell_zero_pos K L v w ν).ne'
      (KcWalkShellIntegral.measure_shell_zero_lt_top K L v w ν).ne
  · exact KcWalkShellIntegral.integral_eq K L v w ν h R hR

end S_TwistedUnipotentTerm_exists_pos_forall_integral_indicator_integralAway_walkShell_eq_mul_add_sum
end P2MW
export P2MW.S_TwistedUnipotentTerm_exists_pos_forall_integral_indicator_integralAway_walkShell_eq_mul_add_sum (solution)

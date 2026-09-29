-- Prove2me | solution 1 for PadicAlgCl.finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1534c94a-8079-585d-89b0-0e0aac0c39a2

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf
import Theorems.Thm_IntermediateField_exists_norm_eq_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow

set_option autoImplicit false

namespace LKWC4

open IntermediateField ExtCitation.LocalLevel

variable (p : ℕ) [hp : Fact p.Prime]

local notation "Ω" => PadicAlgCl p

noncomputable abbrev K0 : IntermediateField ℚ_[p] Ω := ⊥

lemma restrictScalars_adjoin_bot (S : Set Ω) :
    (adjoin (K0 p) S).restrictScalars ℚ_[p] = adjoin ℚ_[p] S := by
  rw [restrictScalars_adjoin_eq_sup, bot_sup_eq]

lemma mem_adjoin_bot_iff (S : Set Ω) (x : Ω) : x ∈ adjoin (K0 p) S ↔ x ∈ adjoin ℚ_[p] S := by
  rw [← mem_restrictScalars ℚ_[p], restrictScalars_adjoin_bot]

lemma algebraMap_botEquiv (x : K0 p) : algebraMap ℚ_[p] Ω (botEquiv ℚ_[p] Ω x) = (x : Ω) := by
  obtain ⟨y, rfl⟩ := (botEquiv ℚ_[p] Ω).symm.surjective x
  rw [AlgEquiv.apply_symm_apply, botEquiv_symm]
  rfl

lemma norm_coe_bot (x : K0 p) : ‖(x : Ω)‖ = ‖botEquiv ℚ_[p] Ω x‖ := by
  rw [← algebraMap_botEquiv, norm_algebraMap']

def bridgeEquiv (S : Set Ω) : adjoin (K0 p) S ≃+* adjoin ℚ_[p] S where
  toFun x := ⟨x.1, (mem_adjoin_bot_iff p S x.1).mp x.2⟩
  invFun x := ⟨x.1, (mem_adjoin_bot_iff p S x.1).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

lemma bridge_comp (S : Set Ω) :
    (algebraMap ℚ_[p] (adjoin ℚ_[p] S)).comp (botEquiv ℚ_[p] Ω).toRingEquiv.toRingHom =
      (bridgeEquiv p S).toRingHom.comp (algebraMap (K0 p) (adjoin (K0 p) S)) := by
  ext y
  change algebraMap ℚ_[p] Ω (botEquiv ℚ_[p] Ω y) = (y : Ω)
  exact algebraMap_botEquiv p y

lemma bridge_comp' (S : Set Ω) :
    (algebraMap ℚ_[p] (adjoin ℚ_[p] S)).comp ((botEquiv ℚ_[p] Ω).toRingEquiv : K0 p →+* ℚ_[p]) =
      ((bridgeEquiv p S) : adjoin (K0 p) S →+* adjoin ℚ_[p] S).comp
        (algebraMap (K0 p) (adjoin (K0 p) S)) := by
  ext y
  change algebraMap ℚ_[p] Ω (botEquiv ℚ_[p] Ω y) = (y : Ω)
  exact algebraMap_botEquiv p y

lemma finrank_bridge (S : Set Ω) :
    Module.finrank (K0 p) (adjoin (K0 p) S) = Module.finrank ℚ_[p] (adjoin ℚ_[p] S) :=
  Algebra.finrank_eq_of_equiv_equiv (botEquiv ℚ_[p] Ω).toRingEquiv (bridgeEquiv p S)
    (bridge_comp p S)

lemma mem_Rw_bot_iff (x : K0 p) : x ∈ Rw p (K0 p) ↔ ‖(x : Ω)‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm]
  rfl

noncomputable def rwBotEquiv : Rw p (K0 p) ≃+* ℤ_[p] where
  toFun x := ⟨botEquiv ℚ_[p] Ω x.1, by rw [← norm_coe_bot]; exact (mem_Rw_bot_iff p x.1).mp x.2⟩
  invFun z := ⟨(botEquiv ℚ_[p] Ω).symm z, by
    rw [mem_Rw_bot_iff, norm_coe_bot, AlgEquiv.apply_symm_apply]; exact z.2⟩
  left_inv x := Subtype.ext ((botEquiv ℚ_[p] Ω).symm_apply_apply x.1)
  right_inv z := Subtype.ext ((botEquiv ℚ_[p] Ω).apply_symm_apply z.1)
  map_mul' x y := Subtype.ext (map_mul (botEquiv ℚ_[p] Ω) x.1 y.1)
  map_add' x y := Subtype.ext (map_add (botEquiv ℚ_[p] Ω) x.1 y.1)

lemma natCard_residueField_Rw_bot :
    Nat.card (IsLocalRing.ResidueField (Rw p (K0 p))) = p := by
  rw [Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv (rwBotEquiv p)).trans
    (PadicInt.residueField (p := p))).toEquiv, Nat.card_zmod]

lemma orderOf_cast_p (n : ℕ) (hn : 0 < n) : orderOf ((p : ℕ) : ZMod (p ^ n - 1)) = n := by
  have hpp := hp.out
  have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hpp.pos
  have key : ((p ^ n : ℕ) : ZMod (p ^ n - 1)) = 1 := by
    have h := ZMod.natCast_self (p ^ n - 1)
    rw [Nat.cast_sub h1, sub_eq_zero, Nat.cast_one] at h
    exact h
  rw [orderOf_eq_iff hn]
  refine ⟨by rw [← Nat.cast_pow, key], fun m hm hm0 h => ?_⟩
  have h' : ((p ^ m : ℕ) : ZMod (p ^ n - 1)) = ((1 : ℕ) : ZMod (p ^ n - 1)) := by
    rw [Nat.cast_pow, Nat.cast_one]; exact h
  rw [ZMod.natCast_eq_natCast_iff] at h'
  have hdvd : p ^ n - 1 ∣ p ^ m - 1 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hpp.pos)).mp h'.symm
  have hlt : p ^ m - 1 < p ^ n - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_pow _ _ hpp.pos) (Nat.pow_lt_pow_right hpp.one_lt hm)
  have hpos : 0 < p ^ m - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hm0.ne' hpp.one_lt)
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)

variable (n : ℕ)

abbrev T : Set Ω := {ζ : Ω | ζ ^ (p ^ n - 1) = 1}

theorem finrank_eq (hn : 0 < n) : Module.finrank ℚ_[p] (adjoin ℚ_[p] (T p n)) = n := by
  have h := IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf p (K0 p) n hn
  rw [natCard_residueField_Rw_bot, orderOf_cast_p p n hn, finrank_bridge] at h
  exact h

theorem norm_eq_zpow (hn : 0 < n) (x : Ω) (hx : x ∈ adjoin ℚ_[p] (T p n)) (hx0 : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = (p : ℝ) ^ k := by
  have hx' : x ∈ adjoin (K0 p) (T p n) := (mem_adjoin_bot_iff p _ x).mpr hx
  obtain ⟨y, hy⟩ := IntermediateField.exists_norm_eq_adjoin_rootsOfUnity_padic p (K0 p) n hn
    ⟨x, hx'⟩ (fun h => hx0 (congrArg Subtype.val h))
  change ‖x‖ = ‖(y : Ω)‖ at hy
  rw [norm_coe_bot] at hy
  set r : ℚ_[p] := botEquiv ℚ_[p] Ω y
  have hr : r ≠ 0 := fun h => by
    rw [h, norm_zero, norm_eq_zero] at hy
    exact hx0 hy
  exact ⟨-r.valuation, by rw [hy, Padic.norm_eq_zpow_neg_valuation hr]⟩

theorem isGalois (hn : 0 < n) : IsGalois ℚ_[p] (adjoin ℚ_[p] (T p n)) := by
  obtain ⟨hfd, hnormal⟩ :=
    IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic p (K0 p) n hn
  haveI := hfd
  haveI := hnormal
  haveI : IsGalois (K0 p) (adjoin (K0 p) (T p n)) := IsGalois.mk
  exact IsGalois.of_equiv_equiv (F := K0 p) (E := adjoin (K0 p) (T p n))
    (f := (botEquiv ℚ_[p] Ω).toRingEquiv) (g := bridgeEquiv p (T p n)) (bridge_comp' p (T p n))

lemma one_le_pow_n : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos

lemma m_pos (hn : 0 < n) : 0 < p ^ n - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' hp.out.one_lt)

lemma not_dvd_m (hn : 0 < n) : ¬ p ∣ p ^ n - 1 := by
  intro h
  have h2 : p ∣ p ^ n - (p ^ n - 1) := Nat.dvd_sub (dvd_pow_self p hn.ne') h
  rw [Nat.sub_sub_self (one_le_pow_n p n)] at h2
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)

lemma norm_natCast_m (hn : 0 < n) : ‖((p ^ n - 1 : ℕ) : Ω)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr (not_dvd_m p n hn)

variable {n}

lemma norm_eq_one_of_pow_eq_one {ζ : Ω} {k : ℕ} (h : ζ ^ k = 1) (hk : k ≠ 0) : ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ k = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).mp h1

lemma norm_geom_sum_le {η : Ω} (hη : ‖η‖ ≤ 1) (i : ℕ) : ‖∑ j ∈ Finset.range i, η ^ j‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hη

theorem eq_one_of_norm_sub_one_lt {η : Ω} {m : ℕ} (hm : 0 < m) (hηm : η ^ m = 1)
    (hnm : ‖(m : Ω)‖ = 1) (hη : ‖η - 1‖ < 1) : η = 1 := by
  by_contra hne
  have hη1 : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one p hηm hm.ne'

  have hsum : ∑ j ∈ Finset.range m, η ^ j = 0 := by
    have := mul_geom_sum η m
    rw [hηm, sub_self, mul_eq_zero] at this
    exact this.resolve_left (sub_ne_zero.mpr hne)

  have hsmall : ∀ j ∈ Finset.range m, ‖η ^ j - 1‖ < 1 := fun j _ => by
    rw [← mul_geom_sum η j, norm_mul]
    calc ‖η - 1‖ * ‖∑ i ∈ Finset.range j, η ^ i‖ ≤ ‖η - 1‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_geom_sum_le p hη1.le j) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hη

  have hne' : (Finset.range m).Nonempty := Finset.nonempty_range_iff.mpr hm.ne'
  obtain ⟨j, hj, hle⟩ :=
    IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne' (fun j => η ^ j - 1)
  have hdecomp : ∑ i ∈ Finset.range m, (η ^ i - 1) = -(m : Ω) := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      zero_sub]
  rw [hdecomp, norm_neg, hnm] at hle
  exact absurd (lt_of_le_of_lt hle (hsmall j hj)) (lt_irrefl _)

theorem eq_of_norm_sub_lt {ζ₁ ζ₂ : Ω} {m : ℕ} (hm : 0 < m) (h₁ : ζ₁ ^ m = 1) (h₂ : ζ₂ ^ m = 1)
    (hnm : ‖(m : Ω)‖ = 1) (h : ‖ζ₁ - ζ₂‖ < 1) : ζ₁ = ζ₂ := by
  have hζ₂ : ‖ζ₂‖ = 1 := norm_eq_one_of_pow_eq_one p h₂ hm.ne'
  have hζ₂0 : ζ₂ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hζ₂; exact zero_ne_one hζ₂
  have hη : (ζ₁ * ζ₂⁻¹) ^ m = 1 := by rw [mul_pow, inv_pow, h₁, h₂, inv_one, mul_one]
  have hdist : ‖ζ₁ * ζ₂⁻¹ - 1‖ < 1 := by
    have : ζ₁ * ζ₂⁻¹ - 1 = (ζ₁ - ζ₂) * ζ₂⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv, hζ₂, inv_one, mul_one]
    exact h
  have := eq_one_of_norm_sub_one_lt p hm hη hnm hdist
  rwa [mul_inv_eq_one₀ hζ₂0] at this

lemma mem_nonunits_iff_norm_lt_one (z : Ω) : z ∈ (padicIntegers p).nonunits ↔ ‖z‖ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  change Valued.v z < 1 ↔ _
  rw [PadicAlgCl.valuation_def, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

theorem exists_frobenius_norm : ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
    ∀ y : Ω, ‖y‖ ≤ 1 → ‖σ y - y ^ p‖ < 1 := by
  obtain ⟨σ, hσ⟩ := exists_frob_local p
  refine ⟨σ, fun y hy => ?_⟩
  have hy' : y ∈ padicIntegers p := by
    rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm]; exact hy
  have := hσ ⟨y, hy'⟩
  rw [mem_nonunits_iff_norm_lt_one] at this
  exact this

lemma norm_algEquiv (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : Ω) : ‖σ y‖ = ‖y‖ :=
  congrArg NNReal.toReal (nnnorm_padicAlgCl_algEquiv p σ y)

theorem norm_pow_apply_sub_lt (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ y : Ω, ‖y‖ ≤ 1 → ‖σ y - y ^ p‖ < 1) (k : ℕ) (y : Ω) (hy : ‖y‖ ≤ 1) :
    ‖(σ ^ k) y - y ^ (p ^ k)‖ < 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, pow_succ, pow_mul]
    have hyk : ‖y ^ (p ^ k)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    calc ‖σ ((σ ^ k) y) - (y ^ p ^ k) ^ p‖
        ≤ max ‖σ ((σ ^ k) y) - σ (y ^ p ^ k)‖ ‖σ (y ^ p ^ k) - (y ^ p ^ k) ^ p‖ := by
          simpa only [dist_eq_norm] using dist_triangle_max (σ ((σ ^ k) y)) (σ (y ^ p ^ k))
            ((y ^ p ^ k) ^ p)
      _ < 1 := max_lt (by rw [← map_sub, norm_algEquiv]; exact ih) (hσ _ hyk)

lemma pow_apply_eq_pow_pow (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {ζ : Ω} {a : ℕ}
    (h : σ ζ = ζ ^ a) (j : ℕ) : (σ ^ j) ζ = ζ ^ (a ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, map_pow, ih, ← pow_mul, ← pow_succ]

lemma apply_eq_self_of_mem_adjoin (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (S : Set Ω)
    (hS : ∀ s ∈ S, τ s = s) {x : Ω} (hx : x ∈ adjoin ℚ_[p] S) : τ x = x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => exact hS y hy
  | algebraMap y => exact AlgEquiv.commutes _ y
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | inv y _ hy => rw [map_inv₀, hy]
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]

private lemma _root_.LKWC4.exists_isPrimitiveRoot (M : ℕ) (hM : 0 < M) : ∃ ζ : Ω, IsPrimitiveRoot ζ M := by
  haveI : NeZero ((M : ℕ) : Ω) := ⟨by exact_mod_cast hM.ne'⟩
  haveI : IsCyclotomicExtension {M} Ω Ω := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot Ω Ω (S := {M}) rfl hM.ne'

p2m_export "LKWC4" "exists_isPrimitiveRoot"

lemma pow_sub_one_eq_prod {m : ℕ} (hm : 0 < m) (x : Ω) :
    x ^ m - 1 = ∏ ζ ∈ Polynomial.nthRootsFinset m (1 : Ω), (x - ζ) := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot p m hm
  have := congrArg (Polynomial.eval x) (Polynomial.X_pow_sub_one_eq_prod hm hζ₀)
  simpa [Polynomial.eval_prod] using this

variable (n)

theorem exists_teichmuller (hn : 0 < n) (x : Ω) (hx : x ∈ adjoin ℚ_[p] (T p n)) (h1 : ‖x‖ = 1) :
    ∃ ζ : Ω, ζ ^ (p ^ n - 1) = 1 ∧ ‖x - ζ‖ < 1 := by
  set m := p ^ n - 1 with hmdef
  have hm : 0 < m := m_pos p n hn
  have hnm : ‖(m : Ω)‖ = 1 := norm_natCast_m p n hn
  have hpn : p ^ n = m + 1 := (Nat.sub_add_cancel (one_le_pow_n p n)).symm
  obtain ⟨σ, hσ⟩ := exists_frobenius_norm p

  have hexact : ∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ p := fun ζ hζ => by
    have hζ1 : ‖ζ‖ ≤ 1 := (norm_eq_one_of_pow_eq_one p hζ hm.ne').le
    refine eq_of_norm_sub_lt p hm ?_ ?_ hnm (hσ ζ hζ1)
    · rw [← map_pow, hζ, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

  have hfixT : ∀ ζ ∈ T p n, (σ ^ n) ζ = ζ := fun ζ (hζ : ζ ^ m = 1) => by
    rw [pow_apply_eq_pow_pow p σ (hexact ζ hζ) n, hpn, pow_succ, hζ, one_mul]
  have hfix : (σ ^ n) x = x := apply_eq_self_of_mem_adjoin p (σ ^ n) (T p n) hfixT hx

  have hlt : ‖x ^ m - 1‖ < 1 := by
    have h := norm_pow_apply_sub_lt p σ hσ n x h1.le
    rw [hfix, hpn, pow_succ, ← norm_neg, neg_sub] at h
    have : x ^ m * x - x = x * (x ^ m - 1) := by ring
    rwa [this, norm_mul, h1, one_mul] at h

  rw [pow_sub_one_eq_prod p hm x, norm_prod] at hlt
  by_contra hcon
  have hge : ∀ ζ ∈ Polynomial.nthRootsFinset m (1 : Ω), ‖x - ζ‖ = 1 := fun ζ hζ => by
    have hζm : ζ ^ m = 1 := (Polynomial.mem_nthRootsFinset hm (1 : Ω)).mp hζ
    refine le_antisymm ?_ (not_lt.mp fun hlt' => hcon ⟨ζ, hζm, hlt'⟩)
    calc ‖x - ζ‖ = ‖x + -ζ‖ := by rw [sub_eq_add_neg]
      _ ≤ max ‖x‖ ‖-ζ‖ := IsUltrametricDist.norm_add_le_max x (-ζ)
      _ = 1 := by rw [norm_neg, h1, norm_eq_one_of_pow_eq_one p hζm hm.ne', max_self]
  rw [Finset.prod_eq_one hge] at hlt
  exact lt_irrefl _ hlt

end LKWC4

theorem solution (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : 0 < n) :
    IsGalois ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ n - 1) = 1}) ∧
    Module.finrank ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ n - 1) = 1}) = n ∧
    (∀ x ∈ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ n - 1) = 1}, x ≠ 0 →
      ∃ k : ℤ, ‖x‖ = (p : ℝ) ^ k) ∧
    (∀ x ∈ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ n - 1) = 1}, ‖x‖ = 1 →
      ∃ ζ : PadicAlgCl p, ζ ^ (p ^ n - 1) = 1 ∧ ‖x - ζ‖ < 1) :=
  ⟨LKWC4.isGalois p n hn, LKWC4.finrank_eq p n hn, LKWC4.norm_eq_zpow p n hn,
    LKWC4.exists_teichmuller p n hn⟩

end S_PadicAlgCl_finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow
end P2MW
export P2MW.S_PadicAlgCl_finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow (solution)

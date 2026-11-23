-- Prove2me | solution 1 for OracleStateHSP.family_isStateHSP
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:32:25.240354+00:00
-- url     : https://prove2.me/submissions/55b4f1dd-9e42-414c-a75d-f7c856328835

import Mathlib
import Definitions.Def_OracleStateHSP_IsStateHSPInstance
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_hiddenSubgroup
import Definitions.Def_OracleStateHSP_flagZero
import Definitions.Def_OracleStateHSP_shiftRep
import Definitions.Def_OracleStateHSP_phiEps
import Definitions.Def_OracleStateHSP_fracU
import Theorems.Thm_OracleStateHSP_fracOracle_unitary_prepares

open OracleStateHSP QAlgorithms

namespace AuxFamily

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma vm_add_self {m : ℕ} (v : V m) : v + v = 0 := by
  ext i; exact zmod2_add_self (v i)

lemma kr_add_self {r : ℕ} (k : K r) : k + k = 0 := by
  ext i; exact zmod2_add_self (k i)

lemma g_add_self {r m : ℕ} (g : K r × V m) : g + g = 0 :=
  Prod.ext (kr_add_self g.1) (vm_add_self g.2)

lemma g_eq_add_iff {r m : ℕ} (x y g : K r × V m) : x = y + g ↔ y = x + g := by
  constructor <;> intro h <;> rw [h, add_assoc, g_add_self, add_zero]

lemma act_shiftRep (r m : ℕ) (g : K r × V m) (ψ : EuclideanSpace ℂ (FlagQ r m))
    (a : Fin 2) (y : K r × V m) (u : V m) :
    act (shiftRep r m g) ψ (a, (y, u)) = ψ (a, (y + g, u)) := by
  simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp]
  have hterm : ∀ q : FlagQ r m,
      shiftRep r m g (a, (y, u)) q * ψ q =
        if q = (a, (y + g, u)) then ψ (a, (y + g, u)) else 0 := by
    rintro ⟨b, ⟨z, v⟩⟩
    have hq_iff : (a = b ∧ y = z + g ∧ u = v) ↔ ((b, (z, v)) : FlagQ r m) = (a, (y + g, u)) := by
      rw [g_eq_add_iff y z g]
      simp [Prod.ext_iff, eq_comm, and_assoc]
    simp only [shiftRep, Matrix.of_apply, hq_iff]
    by_cases h : ((b, (z, v)) : FlagQ r m) = (a, (y + g, u))
    · rw [if_pos h, if_pos h, one_mul, h]
    · rw [if_neg h, if_neg h, zero_mul]
  simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma shiftRep_zero (r m : ℕ) : shiftRep r m 0 = 1 := by
  ext ⟨a, ⟨x, u⟩⟩ ⟨b, ⟨y, v⟩⟩
  simp [shiftRep, Matrix.one_apply, Prod.ext_iff]

lemma shiftRep_add (r m : ℕ) (g h : K r × V m) :
    shiftRep r m (g + h) = shiftRep r m g * shiftRep r m h := by
  ext ⟨a, ⟨x, u⟩⟩ ⟨b, ⟨y, v⟩⟩
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (b, (y + h, v))]
  · simp only [shiftRep, Matrix.of_apply, and_self, ↓reduceIte, mul_one]
    have heq : (x = y + h + g) ↔ (x = y + (g + h)) := by
      rw [add_assoc, add_comm h g]
    simp only [heq]
  · rintro ⟨c, ⟨z, w⟩⟩ _ hne
    have h0 : shiftRep r m h (c, (z, w)) (b, (y, v)) = 0 := by
      simp only [shiftRep, Matrix.of_apply, ite_eq_right_iff]
      rintro ⟨rfl, rfl, rfl⟩
      exact absurd rfl hne
    rw [h0, mul_zero]
  · simp

lemma shiftRep_star (r m : ℕ) (g : K r × V m) :
    star (shiftRep r m g) = shiftRep r m g := by
  ext ⟨a, ⟨x, u⟩⟩ ⟨b, ⟨y, v⟩⟩
  simp only [Matrix.star_apply, shiftRep, Matrix.of_apply, g_eq_add_iff y x g]
  by_cases h : a = b ∧ x = y + g ∧ u = v
  · rw [if_pos ⟨h.1.symm, h.2.1, h.2.2.symm⟩, if_pos h, star_one]
  · have h' : ¬ (b = a ∧ x = y + g ∧ v = u) := fun ⟨h1, h2, h3⟩ => h ⟨h1.symm, h2, h3.symm⟩
    rw [if_neg h', if_neg h, star_zero]

lemma shiftRep_isUnitaryRep (r m : ℕ) : IsUnitaryRep (shiftRep r m) := by
  refine ⟨fun g => ?_, shiftRep_zero r m, shiftRep_add r m⟩
  rw [Matrix.mem_unitaryGroup_iff, shiftRep_star, ← shiftRep_add, g_add_self, shiftRep_zero]

lemma zsmul_vm_mem {m : ℕ} (s : V m) (k : ℤ) : k • s = 0 ∨ k • s = s := by
  rcases Int.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · left
    rw [add_zsmul, ← zsmul_add, vm_add_self, zsmul_zero]
  · right
    have h2 : (2 * t) • s = 0 := by
      rw [mul_comm, mul_zsmul, two_zsmul, vm_add_self, zsmul_zero]
    rw [add_zsmul, h2, one_zsmul, zero_add]

lemma mem_hiddenSubgroup_iff {r m : ℕ} (s : V m) (g : K r × V m) :
    g ∈ hiddenSubgroup r s ↔ (g.2 = 0 ∨ g.2 = s) := by
  simp only [hiddenSubgroup, AddSubgroup.mem_prod, AddSubgroup.mem_top, true_and,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    exact zsmul_vm_mem s k
  · rintro (h0 | hs)
    · exact ⟨0, by simp [h0]⟩
    · exact ⟨1, by simp [hs]⟩

lemma simon_shift_eq_iff {r m : ℕ} (x : SimonInst m) (y g : K r × V m) :
    x.fn (y.2 + g.2) = x.fn y.2 ↔ g ∈ hiddenSubgroup r x.period := by
  unfold SimonInst.fn SimonInst.period
  rw [x.2.1 (y.2 + g.2) y.2, mem_hiddenSubgroup_iff]
  have hy : y.2 + g.2 + y.2 = g.2 := by
    calc y.2 + g.2 + y.2 = g.2 + (y.2 + y.2) := by abel
      _ = g.2 := by rw [vm_add_self, add_zero]
  rw [hy]

lemma act_add_vec {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    act M (v + w) = act M v + act M w := by
  ext i; simp [act, Matrix.mulVec_add]

lemma act_smul_vec {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (c : ℂ) (v : EuclideanSpace ℂ ι) :
    act M (c • v) = c • act M v := by
  ext i; simp [act, Matrix.mulVec_smul]

lemma inner_flag_orthog {r m : ℕ} (v w : EuclideanSpace ℂ (FlagQ r m))
    (hv : ∀ q, v (1, q) = 0) (hw : ∀ q, w (0, q) = 0) :
    inner ℂ v w = 0 ∧ inner ℂ w v = 0 := by
  constructor
  · rw [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [hv, hw]
  · rw [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [hv, hw]

lemma inner_u0_self (r m : ℕ) :
    let u0 : EuclideanSpace ℂ (FlagQ r m) :=
      WithLp.toLp 2 fun p => if p.1 = 0 then uG r m p.2 else 0
    inner ℂ u0 u0 = 1 := by
  intro u0
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [u0, if_true, if_neg h10, inner_zero_right, Finset.sum_const_zero,
    add_zero]
  rw [Fintype.sum_prod_type]
  have hrow : ∀ y : K r × V m,
      (∑ b : V m, inner ℂ (uG r m (y, b)) (uG r m (y, b))) =
        (((2 : ℂ) ^ (r + m))⁻¹) := by
    intro y
    rw [Finset.sum_eq_single (0 : V m)]
    · simp only [uG, WithLp.ofLp_toLp, if_true, RCLike.inner_apply, map_inv₀,
        Complex.conj_ofReal]
      have hsq : ((Real.sqrt (2 ^ (r + m)) : ℂ)) * (Real.sqrt (2 ^ (r + m)) : ℂ) =
          (2 : ℂ) ^ (r + m) := by
        have hr : Real.sqrt ((2 : ℝ) ^ (r + m)) * Real.sqrt ((2 : ℝ) ^ (r + m)) =
            (2 : ℝ) ^ (r + m) := Real.mul_self_sqrt (by positivity)
        exact_mod_cast hr
      rw [← mul_inv, hsq]
    · intro b _ hb0
      simp [uG, hb0]
    · simp
  simp_rw [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
    ZMod.card, Fintype.card_fin, ← pow_add]
  have h2ne : (2 : ℂ) ^ (r + m) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_inv_cancel₀ h2ne]

lemma card_hidden_and_quotient (r m : ℕ) (x : SimonInst m) :
    Nat.card (hiddenSubgroup r x.period) = 2 ^ (r + 1) ∧
    Nat.card ((K r × V m) ⧸ hiddenSubgroup r x.period) = 2 ^ (m - 1) := by
  have hs0 : x.period ≠ 0 := x.2.2
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have : m = 0 := by omega
    subst this
    exact hs0 (Subsingleton.elim _ _)
  let e : K r × Bool ≃ hiddenSubgroup r x.period :=
    { toFun := fun ⟨k, b⟩ => ⟨(k, if b then x.period else 0), by
        rw [mem_hiddenSubgroup_iff]
        cases b <;> simp⟩
      invFun := fun ⟨g, _⟩ => (g.1, decide (g.2 = x.period))
      left_inv := fun ⟨k, b⟩ => by
        cases b
        · simp [hs0.symm]
        · simp
      right_inv := fun ⟨⟨k, v⟩, hg⟩ => by
        rcases (mem_hiddenSubgroup_iff x.period (k, v)).mp hg with rfl | rfl
        · simp [hs0.symm]
        · simp }
  have hcardH : Nat.card (hiddenSubgroup r x.period) = 2 ^ (r + 1) := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, Fintype.card_bool, pow_succ]
  refine ⟨hcardH, ?_⟩
  have hlag := (hiddenSubgroup r x.period).index_mul_card
  change Nat.card ((K r × V m) ⧸ hiddenSubgroup r x.period) *
      Nat.card (hiddenSubgroup r x.period) = Nat.card (K r × V m) at hlag
  have hcardG : Nat.card (K r × V m) = 2 ^ (m - 1) * 2 ^ (r + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, Fintype.card_fin, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [hcardH, hcardG] at hlag
  exact Nat.mul_right_cancel (by positivity) hlag

end AuxFamily

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (r m : ℕ) (x : SimonInst m) :
    (∀ h ∈ hiddenSubgroup r x.period,
        act (shiftRep r m h) (phiEps ε r x.fn) = phiEps ε r x.fn) ∧
    (∀ g, g ∉ hiddenSubgroup r x.period →
        let u0 : EuclideanSpace ℂ (FlagQ r m) :=
          WithLp.toLp 2 fun p => if p.1 = 0 then uG r m p.2 else 0
        let f1 : EuclideanSpace ℂ (FlagQ r m) :=
          WithLp.toLp 2 fun p => if p.1 = 1 then phiF r x.fn p.2 else 0
        inner ℂ (phiEps ε r x.fn) (act (shiftRep r m g) (phiEps ε r x.fn)) =
            ((1 - ε : ℝ) : ℂ) * inner ℂ u0 (act (shiftRep r m g) u0) +
              (ε : ℂ) * inner ℂ f1 (act (shiftRep r m g) f1) ∧
          inner ℂ (phiEps ε r x.fn) (act (shiftRep r m g) (phiEps ε r x.fn)) =
            ((1 - ε : ℝ) : ℂ)) ∧
    IsStateHSPInstance (shiftRep r m) (flagZero r m) (fracU ε r x.fn)
      (hiddenSubgroup r x.period) ε ∧
    Nat.card (hiddenSubgroup r x.period) = 2 ^ (r + 1) ∧
    Nat.card ((K r × V m) ⧸ hiddenSubgroup r x.period) = 2 ^ (m - 1) := by
  have hinv : ∀ h ∈ hiddenSubgroup r x.period,
      act (shiftRep r m h) (phiEps ε r x.fn) = phiEps ε r x.fn := by
    intro h hh
    ext ⟨a, ⟨y, u⟩⟩
    rw [AuxFamily.act_shiftRep]
    have hfn : x.fn (y.2 + h.2) = x.fn y.2 := (AuxFamily.simon_shift_eq_iff x y h).mpr hh
    fin_cases a <;> simp [phiEps, uG, phiF, hfn]
  have hshift : ∀ g, g ∉ hiddenSubgroup r x.period →
      let u0 : EuclideanSpace ℂ (FlagQ r m) :=
        WithLp.toLp 2 fun p => if p.1 = 0 then uG r m p.2 else 0
      let f1 : EuclideanSpace ℂ (FlagQ r m) :=
        WithLp.toLp 2 fun p => if p.1 = 1 then phiF r x.fn p.2 else 0
      inner ℂ (phiEps ε r x.fn) (act (shiftRep r m g) (phiEps ε r x.fn)) =
          ((1 - ε : ℝ) : ℂ) * inner ℂ u0 (act (shiftRep r m g) u0) +
            (ε : ℂ) * inner ℂ f1 (act (shiftRep r m g) f1) ∧
        inner ℂ (phiEps ε r x.fn) (act (shiftRep r m g) (phiEps ε r x.fn)) =
          ((1 - ε : ℝ) : ℂ) := by
    intro g hg u0 f1
    have hdecomp : phiEps ε r x.fn =
        (Real.sqrt (1 - ε) : ℂ) • u0 + (Real.sqrt ε : ℂ) • f1 := by
      ext ⟨a, q⟩
      fin_cases a <;> simp [phiEps, u0, f1]
    have hu0_shift : act (shiftRep r m g) u0 = u0 := by
      ext ⟨a, ⟨y, u⟩⟩
      rw [AuxFamily.act_shiftRep]
      fin_cases a <;> simp [u0, uG]
    have hu0_flag : ∀ q, u0 (1, q) = 0 := fun q => by simp [u0]
    have hf1_flag : ∀ q, f1 (0, q) = 0 := fun q => by simp [f1]
    have hRf1_flag : ∀ q, act (shiftRep r m g) f1 (0, q) = 0 := by
      rintro ⟨y, u⟩
      rw [AuxFamily.act_shiftRep]
      simp [f1]
    obtain ⟨horth1, _⟩ := AuxFamily.inner_flag_orthog u0 (act (shiftRep r m g) f1) hu0_flag hRf1_flag
    obtain ⟨_, horth2⟩ := AuxFamily.inner_flag_orthog (act (shiftRep r m g) u0) f1
      (by rw [hu0_shift]; exact hu0_flag) hf1_flag
    have hlin : inner ℂ (phiEps ε r x.fn) (act (shiftRep r m g) (phiEps ε r x.fn)) =
        ((1 - ε : ℝ) : ℂ) * inner ℂ u0 (act (shiftRep r m g) u0) +
          (ε : ℂ) * inner ℂ f1 (act (shiftRep r m g) f1) := by
      rw [hdecomp, AuxFamily.act_add_vec, AuxFamily.act_smul_vec, AuxFamily.act_smul_vec]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal, horth1, horth2, mul_zero, add_zero, zero_add]
      have hs0 : (Real.sqrt (1 - ε) : ℂ) * (Real.sqrt (1 - ε) : ℂ) = ((1 - ε : ℝ) : ℂ) := by
        have hr : Real.sqrt (1 - ε) * Real.sqrt (1 - ε) = 1 - ε :=
          Real.mul_self_sqrt (by linarith)
        exact_mod_cast hr
      have hs1 : (Real.sqrt ε : ℂ) * (Real.sqrt ε : ℂ) = (ε : ℂ) := by
        have hr : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε0.le
        exact_mod_cast hr
      rw [← mul_assoc, hs0, ← mul_assoc, hs1]
    have hf1_orth : inner ℂ f1 (act (shiftRep r m g) f1) = 0 := by
      rw [PiLp.inner_apply]
      refine Finset.sum_eq_zero fun ⟨a, ⟨y, u⟩⟩ _ => ?_
      rw [AuxFamily.act_shiftRep]
      fin_cases a
      · simp [f1]
      · have hne : x.fn (y.2 + g.2) ≠ x.fn y.2 :=
          mt (AuxFamily.simon_shift_eq_iff x y g).mp hg
        by_cases hu : u = x.fn y.2
        · subst hu
          simp [f1, phiF, hne.symm]
        · simp [f1, phiF, hu]
    have hval : inner ℂ (phiEps ε r x.fn) (act (shiftRep r m g) (phiEps ε r x.fn)) =
        ((1 - ε : ℝ) : ℂ) := by
      rw [hlin, hu0_shift, AuxFamily.inner_u0_self, hf1_orth, mul_one, mul_zero, add_zero]
    exact ⟨hlin, hval⟩
  obtain ⟨_, hU_unit, _, hU_prep, _⟩ :=
    OracleStateHSP.fracOracle_unitary_prepares ε hε0 hε1 r m x.fn
  have hinst : IsStateHSPInstance (shiftRep r m) (flagZero r m) (fracU ε r x.fn)
      (hiddenSubgroup r x.period) ε := by
    refine ⟨AuxFamily.shiftRep_isUnitaryRep r m, hU_unit, hε0, hε1, ?_, ?_⟩
    · intro h hh
      rw [hU_prep]
      exact hinv h hh
    · intro g hg
      rw [hU_prep, (hshift g hg).2, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
  obtain ⟨hcardH, hcardQ⟩ := AuxFamily.card_hidden_and_quotient r m x
  exact ⟨hinv, hshift, hinst, hcardH, hcardQ⟩

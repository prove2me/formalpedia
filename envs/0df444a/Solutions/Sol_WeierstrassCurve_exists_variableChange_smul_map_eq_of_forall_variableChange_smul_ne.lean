-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/dbbd786b-6ee2-5d06-ad4f-10b9cfe08d56

import Mathlib
import Theorems.Thm_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_sq_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open TrivSqZeroExt Module

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "isUnit_Δ VariableChange.one_def VariableChange.map VariableChange.ext a₃ map_map a₁ VariableChange.u map variableChange_a₃ a₄ a₂ a₆ variableChange_a₆ VariableChange.t reduction variableChange_a₂ map_id VariableChange.s map_Δ VariableChange.r variableChange_a₁ variableChange_a₄ Δ VariableChange map_variableChange j VariableChange.eq_one_of_smul_eq_of_sq_eq_bot"
namespace TangentLineAux
p2m_open "WeierstrassCurve"

variable {k : Type} [Field k]

lemma fst_ofNat' (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : DualNumber k)).fst = (OfNat.ofNat n : k) := by
  rw [← Nat.cast_ofNat (R := DualNumber k), TrivSqZeroExt.fst_natCast, Nat.cast_ofNat]

lemma snd_ofNat' (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : DualNumber k)).snd = 0 := by
  rw [← Nat.cast_ofNat (R := DualNumber k), TrivSqZeroExt.snd_natCast]

lemma fstHom_toRingHom_apply (x : DualNumber k) :
    (TrivSqZeroExt.fstHom k k k).toRingHom x = x.fst := rfl

def vec (W : WeierstrassCurve (DualNumber k)) : Fin 5 → k :=
  ![W.a₁.snd, W.a₂.snd, W.a₃.snd, W.a₄.snd, W.a₆.snd]

def par (C : VariableChange (DualNumber k)) : Fin 4 → k :=
  ![(↑C.u⁻¹ : DualNumber k).snd, C.r.snd, C.s.snd, C.t.snd]

def lin (E₀ : WeierstrassCurve k) (m : Fin 4 → k) : Fin 5 → k :=
  ![E₀.a₁ * m 0 + 2 * m 2,
    2 * E₀.a₂ * m 0 + 3 * m 1 - E₀.a₁ * m 2,
    3 * E₀.a₃ * m 0 + E₀.a₁ * m 1 + 2 * m 3,
    4 * E₀.a₄ * m 0 + 2 * E₀.a₂ * m 1 - E₀.a₃ * m 2 - E₀.a₁ * m 3,
    6 * E₀.a₆ * m 0 + E₀.a₄ * m 1 - E₀.a₃ * m 3]

def linMap (E₀ : WeierstrassCurve k) : (Fin 4 → k) →ₗ[k] (Fin 5 → k) where
  toFun := lin E₀
  map_add' x y := by
    ext i
    fin_cases i <;> simp [lin] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [lin] <;> ring

@[scoped simp] lemma linMap_apply (E₀ : WeierstrassCurve k) (m : Fin 4 → k) : linMap E₀ m = lin E₀ m := rfl

section reduction

variable {E₀ : WeierstrassCurve k} {W : WeierstrassCurve (DualNumber k)}

lemma fst_a₁ (hW : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) : W.a₁.fst = E₀.a₁ := by
  simpa [fstHom_toRingHom_apply] using congrArg WeierstrassCurve.a₁ hW
lemma fst_a₂ (hW : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) : W.a₂.fst = E₀.a₂ := by
  simpa [fstHom_toRingHom_apply] using congrArg WeierstrassCurve.a₂ hW
lemma fst_a₃ (hW : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) : W.a₃.fst = E₀.a₃ := by
  simpa [fstHom_toRingHom_apply] using congrArg WeierstrassCurve.a₃ hW
lemma fst_a₄ (hW : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) : W.a₄.fst = E₀.a₄ := by
  simpa [fstHom_toRingHom_apply] using congrArg WeierstrassCurve.a₄ hW
lemma fst_a₆ (hW : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) : W.a₆.fst = E₀.a₆ := by
  simpa [fstHom_toRingHom_apply] using congrArg WeierstrassCurve.a₆ hW

end reduction

lemma eq_of_vec_eq {E₀ : WeierstrassCurve k} {W W' : WeierstrassCurve (DualNumber k)}
    (hW : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀)
    (hW' : W'.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀)
    (h : vec W = vec W') : W = W' := by
  have s1 : W.a₁.snd = W'.a₁.snd := by simpa [vec] using congrFun h 0
  have s2 : W.a₂.snd = W'.a₂.snd := by simpa [vec] using congrFun h 1
  have s3 : W.a₃.snd = W'.a₃.snd := by simpa [vec] using congrFun h 2
  have s4 : W.a₄.snd = W'.a₄.snd := by simpa [vec] using congrFun h 3
  have s6 : W.a₆.snd = W'.a₆.snd := by simpa [vec] using congrFun h 4
  exact WeierstrassCurve.ext
    (TrivSqZeroExt.ext ((fst_a₁ hW).trans (fst_a₁ hW').symm) s1)
    (TrivSqZeroExt.ext ((fst_a₂ hW).trans (fst_a₂ hW').symm) s2)
    (TrivSqZeroExt.ext ((fst_a₃ hW).trans (fst_a₃ hW').symm) s3)
    (TrivSqZeroExt.ext ((fst_a₄ hW).trans (fst_a₄ hW').symm) s4)
    (TrivSqZeroExt.ext ((fst_a₆ hW).trans (fst_a₆ hW').symm) s6)

section infinitesimal

variable {C : VariableChange (DualNumber k)}

lemma fst_coe_u (hC : C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1) : (↑C.u : DualNumber k).fst = 1 := by
  have h := congrArg VariableChange.u hC
  have h' := congrArg (fun v : (k)ˣ => (v : k)) h
  simp [VariableChange.map, fstHom_toRingHom_apply] at h'
  exact h'

lemma fst_coe_u_inv (hC : C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1) :
    (↑C.u⁻¹ : DualNumber k).fst = 1 := by
  have h1 := fst_coe_u hC
  have h2 : ((↑C.u⁻¹ : DualNumber k) * ↑C.u).fst = 1 := by rw [C.u.inv_mul, TrivSqZeroExt.fst_one]
  rw [TrivSqZeroExt.fst_mul, h1, mul_one] at h2
  exact h2

lemma fst_r (hC : C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1) : C.r.fst = 0 := by
  have h__af := congrArg VariableChange.r hC
  simp [VariableChange.map, fstHom_toRingHom_apply] at h__af
  exact h__af
lemma fst_s (hC : C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1) : C.s.fst = 0 := by
  have h__af := congrArg VariableChange.s hC
  simp [VariableChange.map, fstHom_toRingHom_apply] at h__af
  exact h__af
lemma fst_t (hC : C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1) : C.t.fst = 0 := by
  have h__af := congrArg VariableChange.t hC
  simp [VariableChange.map, fstHom_toRingHom_apply] at h__af
  exact h__af

end infinitesimal

lemma vec_smul {E₀ : WeierstrassCurve k} {W : WeierstrassCurve (DualNumber k)}
    (hW : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) {C : VariableChange (DualNumber k)}
    (hC : C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1) :
    vec (C • W) = vec W + lin E₀ (par C) ∧ (C • W).map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ := by
  refine ⟨?_, ?_⟩
  · have hu := fst_coe_u_inv hC
    have hr := fst_r hC
    have hs := fst_s hC
    have ht := fst_t hC
    have h1 := fst_a₁ hW
    have h2 := fst_a₂ hW
    have h3 := fst_a₃ hW
    have h4 := fst_a₄ hW
    have h6 := fst_a₆ hW

    have e1 : (C • W).a₁.snd = W.a₁.snd + (E₀.a₁ * (↑C.u⁻¹ : DualNumber k).snd + 2 * C.s.snd) := by
      simp only [WeierstrassCurve.variableChange_a₁, DualNumber.snd_mul, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_sub,
        TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow, smul_eq_mul, nsmul_eq_mul, Nat.pred_eq_sub_one,
        Nat.reduceSub, fst_ofNat', snd_ofNat', hu, hr, hs, ht, h1, h2, h3, h4, h6, one_pow, pow_one, mul_one,
        mul_zero, zero_mul, add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Nat.cast_ofNat, sub_zero, zero_sub]
      ring
    have e2 : (C • W).a₂.snd = W.a₂.snd + (2 * E₀.a₂ * (↑C.u⁻¹ : DualNumber k).snd + 3 * C.r.snd - E₀.a₁ * C.s.snd) := by
      simp only [WeierstrassCurve.variableChange_a₂, DualNumber.snd_mul, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_sub,
        TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow, smul_eq_mul, nsmul_eq_mul, Nat.pred_eq_sub_one,
        Nat.reduceSub, fst_ofNat', snd_ofNat', hu, hr, hs, ht, h1, h2, h3, h4, h6, one_pow, pow_one, mul_one,
        mul_zero, zero_mul, add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Nat.cast_ofNat, sub_zero, zero_sub]
      ring
    have e3 : (C • W).a₃.snd = W.a₃.snd + (3 * E₀.a₃ * (↑C.u⁻¹ : DualNumber k).snd + E₀.a₁ * C.r.snd + 2 * C.t.snd) := by
      simp only [WeierstrassCurve.variableChange_a₃, DualNumber.snd_mul, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_sub,
        TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow, smul_eq_mul, nsmul_eq_mul, Nat.pred_eq_sub_one,
        Nat.reduceSub, fst_ofNat', snd_ofNat', hu, hr, hs, ht, h1, h2, h3, h4, h6, one_pow, pow_one, mul_one,
        mul_zero, zero_mul, add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Nat.cast_ofNat, sub_zero, zero_sub]
      ring
    have e4 : (C • W).a₄.snd = W.a₄.snd + (4 * E₀.a₄ * (↑C.u⁻¹ : DualNumber k).snd + 2 * E₀.a₂ * C.r.snd
        - E₀.a₃ * C.s.snd - E₀.a₁ * C.t.snd) := by
      simp only [WeierstrassCurve.variableChange_a₄, DualNumber.snd_mul, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_sub,
        TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow, smul_eq_mul, nsmul_eq_mul, Nat.pred_eq_sub_one,
        Nat.reduceSub, fst_ofNat', snd_ofNat', hu, hr, hs, ht, h1, h2, h3, h4, h6, one_pow, pow_one, mul_one,
        mul_zero, zero_mul, add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Nat.cast_ofNat, sub_zero, zero_sub]
      ring
    have e6 : (C • W).a₆.snd = W.a₆.snd + (6 * E₀.a₆ * (↑C.u⁻¹ : DualNumber k).snd + E₀.a₄ * C.r.snd
        - E₀.a₃ * C.t.snd) := by
      simp only [WeierstrassCurve.variableChange_a₆, DualNumber.snd_mul, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_sub,
        TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow, smul_eq_mul, nsmul_eq_mul, Nat.pred_eq_sub_one,
        Nat.reduceSub, fst_ofNat', snd_ofNat', hu, hr, hs, ht, h1, h2, h3, h4, h6, one_pow, pow_one, mul_one,
        mul_zero, zero_mul, add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Nat.cast_ofNat, sub_zero, zero_sub]
      ring
    ext i
    fin_cases i
    · simpa [vec, par, lin] using e1
    · simpa [vec, par, lin] using e2
    · simpa [vec, par, lin] using e3
    · simpa [vec, par, lin] using e4
    · simpa [vec, par, lin] using e6
  · rw [← WeierstrassCurve.map_variableChange, hC, hW, one_smul]

def chg (m : Fin 4 → k) : VariableChange (DualNumber k) where
  u := ⟨inl 1 + inr (-(m 0)), inl 1 + inr (m 0),
    by
      apply TrivSqZeroExt.ext
      · simp [TrivSqZeroExt.fst_mul]
      · simp [DualNumber.snd_mul],
    by
      apply TrivSqZeroExt.ext
      · simp [TrivSqZeroExt.fst_mul]
      · simp [DualNumber.snd_mul]⟩
  r := inr (m 1)
  s := inr (m 2)
  t := inr (m 3)

lemma coe_chg_u_inv (m : Fin 4 → k) : (↑(chg m).u⁻¹ : DualNumber k) = inl 1 + inr (m 0) := rfl

lemma coe_chg_u (m : Fin 4 → k) : (↑(chg m).u : DualNumber k) = inl 1 + inr (-(m 0)) := rfl

lemma par_chg (m : Fin 4 → k) : par (chg m) = m := by
  ext i
  fin_cases i
  · simp [par, coe_chg_u_inv]
  · simp [par, chg]
  · simp [par, chg]
  · simp [par, chg]

lemma chg_map (m : Fin 4 → k) : (chg m).map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 := by
  rw [VariableChange.one_def]
  refine VariableChange.ext ?_ ?_ ?_ ?_
  · refine Units.ext ?_
    show (TrivSqZeroExt.fstHom k k k).toRingHom (↑(chg m).u : DualNumber k) = 1
    rw [fstHom_toRingHom_apply, coe_chg_u]
    simp
  · show (TrivSqZeroExt.fstHom k k k).toRingHom (inr (m 1)) = 0
    simp [fstHom_toRingHom_apply]
  · show (TrivSqZeroExt.fstHom k k k).toRingHom (inr (m 2)) = 0
    simp [fstHom_toRingHom_apply]
  · show (TrivSqZeroExt.fstHom k k k).toRingHom (inr (m 3)) = 0
    simp [fstHom_toRingHom_apply]

lemma par_one : par (1 : VariableChange (DualNumber k)) = 0 := by
  ext i
  fin_cases i <;> simp [par, VariableChange.one_def]

lemma triv_map (E₀ : WeierstrassCurve k) :
    (E₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ := by
  rw [WeierstrassCurve.map_map]
  have : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k))) = RingHom.id k := by
    ext x
    simp [fstHom_toRingHom_apply, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this, WeierstrassCurve.map_id]

lemma vec_triv (E₀ : WeierstrassCurve k) : vec (E₀.map (algebraMap k (DualNumber k))) = 0 := by
  ext i
  fin_cases i <;> simp [vec, TrivSqZeroExt.algebraMap_eq_inl]

lemma ker_sq_eq_bot : (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [RingHom.mem_ker, fstHom_toRingHom_apply] at hx hy
  rw [Ideal.mem_bot]
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_mul, hx]
  · simp [DualNumber.snd_mul, hx, hy]

lemma lin_eq_zero {E₀ : WeierstrassCurve k} [E₀.IsElliptic] {m : Fin 4 → k} (hm : lin E₀ m = 0) : m = 0 := by
  set W := E₀.map (algebraMap k (DualNumber k)) with hWdef
  have hW := triv_map E₀
  have hvW := vec_triv E₀
  obtain ⟨hvec, hmap⟩ := vec_smul hW (chg_map m)
  rw [par_chg, hm, add_zero] at hvec
  have hfix : chg m • W = W := eq_of_vec_eq hmap hW hvec
  have hΔ : IsUnit W.Δ := by
    rw [hWdef, WeierstrassCurve.map_Δ]
    exact E₀.isUnit_Δ.map _
  have hone : chg m = 1 :=
    WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_sq_eq_bot W hΔ
      (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) ker_sq_eq_bot (chg m)
      (by rw [RingHom.mem_ker, map_sub, map_one, fstHom_toRingHom_apply, coe_chg_u]; simp)
      (by rw [RingHom.mem_ker, fstHom_toRingHom_apply]; simp [chg])
      (by rw [RingHom.mem_ker, fstHom_toRingHom_apply]; simp [chg])
      (by rw [RingHom.mem_ker, fstHom_toRingHom_apply]; simp [chg])
      hfix
  have := par_chg m
  rw [hone, par_one] at this
  exact this.symm

lemma linMap_injective (E₀ : WeierstrassCurve k) [E₀.IsElliptic] : Function.Injective (linMap E₀) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  exact lin_eq_zero hm

lemma exists_eq_smul_add_lin (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (v₁ : Fin 5 → k)
    (hv₁ : ∀ m, lin E₀ m ≠ v₁) (v : Fin 5 → k) : ∃ (c : k) (m : Fin 4 → k), v = c • v₁ + lin E₀ m := by
  set N : Submodule k (Fin 5 → k) := LinearMap.range (linMap E₀) with hN
  have hrange : finrank k N = 4 := by
    rw [hN, LinearMap.finrank_range_of_inj (linMap_injective E₀), Module.finrank_fin_fun]
  have hq : finrank k ((Fin 5 → k) ⧸ N) = 1 := by
    have h := N.finrank_quotient_add_finrank
    rw [hrange, Module.finrank_fin_fun] at h
    omega
  have hnz : N.mkQ v₁ ≠ 0 := by
    intro h0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN, LinearMap.mem_range] at h0
    obtain ⟨m, hm⟩ := h0
    exact hv₁ m (by simpa using hm)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (N.mkQ v₁) hnz).1 hq (N.mkQ v)
  have hmem : v - c • v₁ ∈ N := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, hc, sub_self]
  rw [hN, LinearMap.mem_range] at hmem
  obtain ⟨m, hm⟩ := hmem
  refine ⟨c, m, ?_⟩
  rw [linMap_apply] at hm
  rw [hm]
  abel

lemma map_scale {E₀ : WeierstrassCurve k} {E₁ : WeierstrassCurve (DualNumber k)}
    (hE₁ : E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) (c : k) :
    (E₁.map (TrivSqZeroExt.map (c • LinearMap.id : k →ₗ[k] k)).toRingHom).map
        (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      vec (E₁.map (TrivSqZeroExt.map (c • LinearMap.id : k →ₗ[k] k)).toRingHom) = c • vec E₁ := by
  constructor
  · rw [WeierstrassCurve.map_map]
    have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp
        (TrivSqZeroExt.map (c • LinearMap.id : k →ₗ[k] k)).toRingHom =
        (TrivSqZeroExt.fstHom k k k).toRingHom :=
      RingHom.ext fun x => by simp [fstHom_toRingHom_apply]
    rw [this, hE₁]
  · ext i
    fin_cases i <;> simp [vec]

end WeierstrassCurve.TangentLineAux
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne.WeierstrassCurve.TangentLineAux"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne.WeierstrassCurve"

open WeierstrassCurve.TangentLineAux in

theorem solution
    (k : Type) [Field k] (E₀ : WeierstrassCurve k) [E₀.IsElliptic]
    (E₁ : WeierstrassCurve (DualNumber k)) (hE₁ : E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀)
    (hE₁' : ∀ C : WeierstrassCurve.VariableChange (DualNumber k),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 → C • (E₀.map (algebraMap k (DualNumber k))) ≠ E₁)
    (E : WeierstrassCurve (DualNumber k)) (hE : E.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) :
    ∃ (c : k) (C : WeierstrassCurve.VariableChange (DualNumber k)),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 ∧
      C • (E₁.map (TrivSqZeroExt.map (c • LinearMap.id : k →ₗ[k] k)).toRingHom) = E := by

  have hv₁ : ∀ m, lin E₀ m ≠ vec E₁ := by
    intro m hm
    apply hE₁' (chg m) (chg_map m)
    obtain ⟨hvec, hmap⟩ := vec_smul (triv_map E₀) (chg_map m)
    rw [par_chg, vec_triv, zero_add, hm] at hvec
    exact eq_of_vec_eq hmap hE₁ hvec

  obtain ⟨c, m, hcm⟩ := exists_eq_smul_add_lin E₀ (vec E₁) hv₁ (vec E)
  obtain ⟨hmap₁, hvec₁⟩ := map_scale hE₁ c
  refine ⟨c, chg m, chg_map m, ?_⟩
  obtain ⟨hvec, hmap⟩ := vec_smul hmap₁ (chg_map m)
  rw [par_chg, hvec₁, ← hcm] at hvec
  exact eq_of_vec_eq hmap hE hvec

end S_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne (solution)

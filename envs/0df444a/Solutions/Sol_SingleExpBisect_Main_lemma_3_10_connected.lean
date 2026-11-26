-- Prove2me | solution 1 for SingleExpBisect.Main.lemma_3_10_connected
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:32:38.828152+00:00
-- url     : https://prove2.me/submissions/0d79d95f-29bd-4106-9adb-f625a0ffacfb

/- Cut-edge, submodularity, and attainment lemmas adapted from Secousses, Prove2Me submission 797eedb1-a223-4590-b528-4b3d16d0ab3c (Apache-2.0). -/
import Mathlib
import Definitions.Def_SingleExpBisect_Main_NodeData
import Definitions.Def_SingleExpBisect_Main_Graphs
import Theorems.Thm_SingleExpBisect_Main_lemma_3_7
import Theorems.Thm_SingleExpBisect_Main_lemma_3_8

set_option autoImplicit false

open scoped Classical

open SingleExpBisect.Main

open MinBisectFPT

open scoped Classical BigOperators
open SingleExpBisect.Main
namespace ExpLogProof

open PowerSeries in
lemma exp_at_log :
    (PowerSeries.exp ℚ).subst (PowerSeries.log ℚ) = (1 + PowerSeries.X : PowerSeries ℚ) := by
  let E : PowerSeries ℚ := (exp ℚ).subst (log ℚ)
  let Q : PowerSeries ℚ := 1 + X
  have shift (A : PowerSeries ℚ) (n : ℕ) :
      coeff (n+1) (A * X) = coeff n A := by
    simpa using coeff_mul_X_pow A 1 n
  have hg : derivative ℚ (log ℚ) * Q = 1 := by
    rw [deriv_log]
    ext n
    cases n with
    | zero => simp [Q, coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_mk]
    | succ n =>
      simp only [Q, mul_add, mul_one, map_add, shift, coeff_mk, coeff_one,
        Nat.succ_ne_zero, if_false, Algebra.algebraMap_self_apply]
      rw [pow_succ]
      ring
  have hd : derivative ℚ E * Q = E := by
    dsimp only [E]
    rw [derivative_subst HasSubst.log, derivative_exp, mul_assoc, hg, mul_one]
  have hQ : derivative ℚ Q * Q = Q := by simp [Q, derivative_one]
  let R := E - Q
  have hR : derivative ℚ R * Q = R := by simp only [R, map_sub, sub_mul, hd, hQ]
  have hc : constantCoeff E = 1 := by
    change MvPowerSeries.constantCoeff ((exp ℚ).subst (log ℚ)) = 1
    rw [constantCoeff_subst HasSubst.log]
    rw [finsum_eq_single _ 0]
    · simp
    · intro n hn
      simp [map_pow, ← PowerSeries.constantCoeff_eq, zero_pow hn]
  have hzero : R = 0 := by
    ext n
    change coeff n R = 0
    induction n with
    | zero => simp [R,Q,coeff_zero_eq_constantCoeff,hc]
    | succ n ih =>
      have hh := congrArg (coeff n) hR
      change coeff n (derivative ℚ R * (1+X)) = coeff n R at hh
      rw [mul_add, mul_one, map_add, coeff_derivative, ih] at hh
      have hshift : coeff n (derivative ℚ R * X) = 0 := by
        cases n with
        | zero => simp [coeff_zero_eq_constantCoeff]
        | succ k => rw [shift,coeff_derivative,ih,zero_mul]
      rw [hshift,add_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_right (by positivity)
  exact sub_eq_zero.mp hzero

lemma finite_subst {σ : Type} (A : MvPowerSeries σ ℚ)
    (hA : A.constantCoeff = 0) (F : PowerSeries ℚ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (F.subst A) =
      ∑ j ∈ Finset.range (m.degree + 1),
        PowerSeries.coeff j F * MvPowerSeries.coeff m (A ^ j) := by
  rw [PowerSeries.coeff_subst (.of_constantCoeff_zero hA)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra h
  have hj' : m.degree < j := by simpa using h
  have hz := MvPowerSeries.coeff_of_lt_order (f := A^j) (d := m)
    (lt_of_lt_of_le (by exact_mod_cast hj') (A.le_order_pow_of_constantCoeff_eq_zero j hA))
  exact hj (by simp [hz])

lemma expPS_eq {σ : Type} (A : MvPowerSeries σ ℚ) (hA : A.constantCoeff = 0) :
    expPS A = (PowerSeries.exp ℚ).subst A := by
  ext m
  rw [finite_subst A hA]
  change (∑ j ∈ Finset.range (m.degree + 1), _ * _) = _
  simp

lemma logPS_eq {σ : Type} (A : MvPowerSeries σ ℚ) (hA : A.constantCoeff = 1) :
    logPS A = (PowerSeries.log ℚ).subst (A-1) := by
  ext m
  rw [finite_subst (A-1) (by simp [hA])]
  change (∑ j ∈ Finset.Icc 1 m.degree, _ * _) = _
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m.degree+1)) (fun j => 0 < j)]
  have heq : (Finset.range (m.degree+1)).filter (fun j => 0 < j) = Finset.Icc 1 m.degree := by
    ext j; simp; omega
  rw [heq]
  have hzero : ∑ j ∈ (Finset.range (m.degree+1)).filter (fun j => ¬ 0 < j),
      PowerSeries.coeff j (PowerSeries.log ℚ) * MvPowerSeries.coeff m ((A-1)^j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have : j = 0 := by have := (Finset.mem_filter.mp hj).2; omega
    simp [this]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp [show j ≠ 0 by have := (Finset.mem_Icc.mp hj).1; omega]

lemma pow_congr_off {σ : Type} (U : Set (σ →₀ ℕ)) (hU : IsUpClosed U)
    (F G : MvPowerSeries σ ℚ)
    (h : ∀ m ∉ U, MvPowerSeries.coeff m F = MvPowerSeries.coeff m G)
    (n : ℕ) : ∀ m ∉ U, MvPowerSeries.coeff m (F^n) = MvPowerSeries.coeff m (G^n) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    intro m hm
    simp only [pow_succ, MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨a,b⟩ hab
    have hsum : a+b=m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have ha : a ∉ U := fun hu => hm (hsum ▸ hU a hu b)
    have hb : b ∉ U := fun hu => hm ((add_comm a b ▸ hsum) ▸ hU b hu a)
    rw [ih a ha, h b hb]

end ExpLogProof

open scoped Classical BigOperators
open SingleExpBisect.Main
namespace ExpLogProof
open MvPowerSeries

private def jetIdeal {σ : Type} (d : ℕ) : Ideal (MvPowerSeries σ ℚ) where
  carrier := {F | (d : ℕ∞) ≤ F.order}
  zero_mem' := by simp
  add_mem' := fun ha hb => (le_min ha hb).trans min_order_le_add
  smul_mem' := fun a b hb =>
    calc
      (d : ℕ∞) ≤ b.order := hb
      _ ≤ a.order + b.order := le_add_self
      _ ≤ (a*b).order := le_order_mul

private lemma expImage {σ : Type} (d : ℕ) (A : MvPowerSeries σ ℚ) (hA : A.constantCoeff = 0) :
    Ideal.Quotient.mkₐ ℚ (jetIdeal (σ := σ) (d+1)) (expPS A) =
    IsNilpotent.exp (Ideal.Quotient.mkₐ ℚ (jetIdeal (σ := σ) (d+1)) A) := by
  classical
  let q := Ideal.Quotient.mkₐ ℚ (jetIdeal (σ := σ) (d+1))
  have hnil : (q A)^(d+1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (A.le_order_pow_of_constantCoeff_eq_zero (d+1) hA)
  change q _ = IsNilpotent.exp (q A)
  rw [IsNilpotent.exp_eq_sum hnil]
  let P := ∑ j ∈ Finset.range (d+1), (j.factorial : ℚ)⁻¹ • A^j
  have hp : q P = ∑ j ∈ Finset.range (d+1), (j.factorial : ℚ)⁻¹ • (q A)^j := by
    simp [P]
  rw [←hp]
  apply Ideal.Quotient.eq.mpr
  apply MvPowerSeries.nat_le_order
  intro m hm
  change coeff m (expPS A - P) = 0
  rw [map_sub, sub_eq_zero]
  simp only [P, map_sum, coeff_smul]
  change (∑ j ∈ Finset.range (m.degree+1), (1 / (j.factorial : ℚ)) * _) = _
  simp only [one_div]
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono (by omega))
  · intro j hj
    have hlt : m.degree < j := by simpa using (Finset.mem_sdiff.mp hj).2
    rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt)
       (A.le_order_pow_of_constantCoeff_eq_zero j hA)), mul_zero]
  · intros; rfl

lemma exp_add_zero {σ : Type} (A B : MvPowerSeries σ ℚ)
    (hA : A.constantCoeff=0) (hB : B.constantCoeff=0) :
    expPS (A+B) = expPS A * expPS B := by
  classical
  ext m
  let q := Ideal.Quotient.mkₐ ℚ (jetIdeal (σ := σ) (m.degree+1))
  have hn (F : MvPowerSeries σ ℚ) (hF : F.constantCoeff=0) : IsNilpotent (q F) := by
    refine ⟨m.degree+1, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (F.le_order_pow_of_constantCoeff_eq_zero _ hF)
  have hq : q (expPS (A+B)) = q (expPS A * expPS B) := by
    rw [map_mul, expImage _ (A+B) (by simp [hA,hB]), expImage _ A hA, expImage _ B hB,
      map_add]
    exact IsNilpotent.exp_add_of_commute (Commute.all _ _) (hn _ hA) (hn _ hB)
  have hz : (↑(m.degree+1) : ℕ∞) ≤ (expPS (A+B) - expPS A * expPS B).order :=
    Ideal.Quotient.eq.mp hq
  have hh := coeff_of_lt_order (d := m) (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m.degree) hz)
  simpa only [map_sub, sub_eq_zero] using hh

private noncomputable def compQQ (F G : PowerSeries ℚ) : PowerSeries ℚ := PowerSeries.subst G F

open PowerSeries in
private lemma log_at_exp :
    (log ℚ).subst (exp ℚ - 1) = (PowerSeries.X : PowerSeries ℚ) := by
  let L : PowerSeries ℚ := log ℚ
  let E : PowerSeries ℚ := exp ℚ - 1
  have hL : L.constantCoeff=0 := constantCoeff_log
  have hu : IsUnit (L.coeff 1) := by simp [L]
  let I : PowerSeries ℚ := L.substInvOfIsUnit hu
  have hI : PowerSeries.HasSubst I := PowerSeries.HasSubst.substInvOfIsUnit L hu
  have hLI : compQQ L I = PowerSeries.X := subst_substInvOfIsUnit_right L hL hu
  have hEL : compQQ E L = PowerSeries.X := by
    change (exp ℚ - 1).subst (log ℚ) = (PowerSeries.X : PowerSeries ℚ)
    rw [PowerSeries.subst_sub PowerSeries.HasSubst.log, exp_at_log]
    have hone : PowerSeries.subst (R := ℚ) (log ℚ) 1 = 1 := by
      rw [← PowerSeries.coe_substAlgHom PowerSeries.HasSubst.log, map_one]
    rw [hone]; ring
  have hAssoc : compQQ E (compQQ L I) = compQQ (compQQ E L) I :=
    (PowerSeries.subst_comp_subst_apply (R := ℚ) (a := L) (b := I) PowerSeries.HasSubst.log hI E).symm
  rw [hLI, hEL] at hAssoc
  have heX : compQQ E PowerSeries.X = E := PowerSeries.X_subst E
  have hXI : compQQ PowerSeries.X I = I := PowerSeries.subst_X hI
  rw [heX, hXI] at hAssoc
  change compQQ L E = PowerSeries.X
  rwa [hAssoc]

lemma log_exp_zero {σ : Type} (A : MvPowerSeries σ ℚ) (hA : A.constantCoeff=0) :
    logPS (expPS A) = A := by
  have hE : (expPS A).constantCoeff=1 := by
    change coeff 0 (expPS A)=1
    change (∑ j ∈ Finset.range ((0 : σ →₀ ℕ).degree+1), (1/(j.factorial:ℚ)) * coeff 0 (A^j)) = 1
    simp
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hA
  have hE1 : PowerSeries.HasSubst (PowerSeries.exp ℚ - 1) :=
    .of_constantCoeff_zero (by simp [← PowerSeries.constantCoeff_eq])
  rw [logPS_eq _ hE, expPS_eq A hA]
  have heq : (PowerSeries.exp ℚ).subst A - 1 = (PowerSeries.exp ℚ - 1).subst A := by
    rw [← PowerSeries.coe_substAlgHom hs, map_sub, map_one]
  rw [heq, ← PowerSeries.subst_comp_subst_apply hE1 hs, log_at_exp, PowerSeries.subst_X hs]

lemma logPS_mul {σ : Type} (A B : MvPowerSeries σ ℚ)
    (hA : A.constantCoeff=1) (hB : B.constantCoeff=1) :
    logPS (A*B) = logPS A + logPS B := by
  have aux (F : MvPowerSeries σ ℚ) (hF : F.constantCoeff=1) :
      (logPS F).constantCoeff=0 ∧ expPS (logPS F)=F := by
    have hz : (F-1).constantCoeff=0 := by simp [hF]
    have hl : (logPS F).constantCoeff=0 := by
      rw [logPS_eq _ hF]; exact PowerSeries.constantCoeff_subst_eq_zero hz _ PowerSeries.constantCoeff_log
    refine ⟨hl, ?_⟩
    rw [expPS_eq _ hl, logPS_eq _ hF, ← PowerSeries.subst_comp_subst_apply
      PowerSeries.HasSubst.log (PowerSeries.HasSubst.of_constantCoeff_zero hz), exp_at_log]
    rw [← PowerSeries.coe_substAlgHom (.of_constantCoeff_zero hz)]
    simp [PowerSeries.substAlgHom_X]
  obtain ⟨hzA, heA⟩ := aux A hA
  obtain ⟨hzB, heB⟩ := aux B hB
  rw [← log_exp_zero (logPS A + logPS B) (by simp [hzA,hzB]), exp_add_zero _ _ hzA hzB, heA, heB]

lemma logPS_congr_off {σ : Type} (U : Set (σ →₀ ℕ)) (hU : IsUpClosed U)
    (F G : MvPowerSeries σ ℚ)
    (h : ∀ m ∉ U, MvPowerSeries.coeff m F = MvPowerSeries.coeff m G)
    (m : σ →₀ ℕ) (hm : m ∉ U) : coeff m (logPS F) = coeff m (logPS G) := by
  classical
  change (∑ j ∈ Finset.Icc 1 m.degree, _ * _) = (∑ j ∈ Finset.Icc 1 m.degree, _ * _)
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply pow_congr_off U hU _ _ _ j m hm
  intro a ha
  simp only [map_sub, h a ha]

end ExpLogProof

open scoped Classical BigOperators
open SingleExpBisect.Main
namespace CutFactors

private noncomputable def term {n : ℕ} (f : Finset (Fin n) → ℕ) (R : Finset (Fin n)) :
    MvPolynomial (Var n) ℚ :=
  MvPolynomial.monomial (Finsupp.single Var.w (f R) + yMono R) 1

noncomputable def block {n : ℕ} (f : Finset (Fin n) → ℕ) (A : Finset (Fin n)) :
    MvPolynomial (Var n) ℚ := ∑ R ∈ A.powerset, term f R

private lemma ymono_apply {n : ℕ} (R : Finset (Fin n)) (v : Fin n) :
    (yMono R) (Var.y v) = if v ∈ R then 1 else 0 := by
  classical
  simp [yMono, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]

private lemma ymono_w {n : ℕ} (R : Finset (Fin n)) : (yMono R) Var.w = 0 := by
  simp [yMono, Finsupp.finsetSum_apply, Finsupp.single_apply]

private lemma mono_union {n : ℕ} {U V : Finset (Fin n)} (hUV : Disjoint U V) :
    yMono (U ∪ V) = yMono U + yMono V := Finset.sum_union hUV

lemma block_mul {n : ℕ} (f : Finset (Fin n) → ℕ) (A B : Finset (Fin n)) (hdis : Disjoint A B)
    (hadd : ∀ R ⊆ A ∪ B, f R = f (R ∩ A) + f (R ∩ B)) :
    block f (A ∪ B) = block f A * block f B := by
  classical
  unfold block
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have recover (U V : Finset (Fin n)) (hU : U ⊆ A) (hV : V ⊆ B) :
      (U ∪ V) ∩ A = U ∧ (U ∪ V) ∩ B = V := by
    constructor <;> ext x <;> simp only [Finset.mem_union, Finset.mem_inter]
    · have hd : x ∈ V → x ∈ A → False := fun hv ha => Finset.disjoint_left.mp hdis ha (hV hv)
      exact ⟨fun hx => hx.1.elim id (fun h => False.elim (hd h hx.2)), fun h => ⟨Or.inl h,hU h⟩⟩
    · have hd : x ∈ U → x ∈ B → False := fun hu hb => Finset.disjoint_left.mp hdis (hU hu) hb
      exact ⟨fun hx => hx.1.elim (fun h => False.elim (hd h hx.2)) id, fun h => ⟨Or.inr h,hV h⟩⟩
  have reun (R : Finset (Fin n)) (hR : R ⊆ A ∪ B) : R ∩ A ∪ R ∩ B = R := by
    ext v
    have h := @hR v
    simp only [Finset.mem_inter, Finset.mem_union] at *
    tauto
  apply Finset.sum_bij (fun R _ => (R ∩ A, R ∩ B))
  · intro R _
    simp [Finset.inter_subset_right]
  · intro R hR T hT heq
    rw [←reun R (Finset.mem_powerset.mp hR), ←reun T (Finset.mem_powerset.mp hT)]
    exact congrArg₂ (fun (u v : Finset (Fin n)) => u ∪ v) (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  · rintro ⟨U,V⟩ huv
    obtain ⟨hU,hV⟩ := Finset.mem_product.mp huv
    have hh := recover U V (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV)
    exact ⟨U ∪ V, Finset.mem_powerset.mpr (Finset.union_subset_union (Finset.mem_powerset.mp hU)
      (Finset.mem_powerset.mp hV)), Prod.ext hh.1 hh.2⟩
  · intro R hR
    have hR' := Finset.mem_powerset.mp hR
    have hd : Disjoint (R∩A) (R∩B) := hdis.mono (Finset.inter_subset_right) (Finset.inter_subset_right)
    have hy := (mono_union hd).symm
    rw [reun R hR'] at hy
    simp only [term, MvPolynomial.monomial_mul, one_mul]
    rw [hadd R hR', Finsupp.single_add, ←hy]
    abel

private lemma subterm {n : ℕ} (f : Finset (Fin n) → ℕ) {e : Var n →₀ ℕ}
    (R : Finset (Fin n)) (hn : MvPolynomial.coeff e (term f R) ≠ 0) :
    (∀ v ∈ R, 0 < e (.y v)) ∧ e .w = f R := by
  classical
  have he : Finsupp.single Var.w (f R) + yMono R = e := by
    by_contra hx
    simp [term, MvPolynomial.coeff_monomial, hx, Ne.symm hx] at hn
  subst e
  constructor
  · intro v hv
    simp [Finsupp.single_apply, ymono_apply, hv]
  · simp [Finsupp.single_apply, ymono_w]

lemma restricted_coeff {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (k : ℕ)
    (e m : Var n →₀ ℕ) (hm : m ≤ e) (hk : e .w ≤ k) :
    MvPolynomial.coeff m (Zfull G W k) =
      MvPolynomial.coeff m (block (mu G W) (W.filter fun v => 0 < e (.y v))) := by
  classical
  let S := W.filter fun v => 0 < e (.y v)
  let f := mu G W
  let a := W.powerset.filter (fun R => f R ≤ k)
  let b := S.powerset
  let c := W.powerset
  have ha : a ⊆ c := Finset.filter_subset _ _
  have hb : b ⊆ c := Finset.powerset_mono.mpr (Finset.filter_subset _ _)
  change MvPolynomial.coeff m (∑ R ∈ a, term f R) = MvPolynomial.coeff m (∑ R ∈ b, term f R)
  simp only [MvPolynomial.coeff_sum]
  trans ∑ R ∈ c, MvPolynomial.coeff m (term f R)
  · apply Finset.sum_subset ha
    intro R hR hRa
    by_contra hn
    exact hRa (Finset.mem_filter.mpr ⟨hR, (subterm f R hn).2 ▸ (hm Var.w).trans hk⟩)
  · symm
    apply Finset.sum_subset hb
    intro R hR hRb
    by_contra hn
    apply hRb
    apply Finset.mem_powerset.mpr
    intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_powerset.mp hR) hv,
      ((subterm f R hn).1 v hv).trans_le (hm (.y v))⟩

lemma block_const {n : ℕ} (f : Finset (Fin n) → ℕ) (hf : f ∅=0) (A : Finset (Fin n)) :
    ((block f A : MvPowerSeries (Var n) ℚ)).constantCoeff = 1 := by
  classical
  change MvPolynomial.coeff 0 (block f A) = 1
  rw [block, MvPolynomial.coeff_sum, Finset.sum_eq_single ∅]
  · simp [term, hf, yMono, MvPolynomial.coeff_monomial]
  · intro R hR hne
    by_contra hn
    obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact (Nat.lt_irrefl 0) ((subterm f R hn).1 v hv)
  · simp

lemma block_support {n : ℕ} (f : Finset (Fin n) → ℕ) (A : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ A) (e : Var n →₀ ℕ)
    (hn : MvPowerSeries.coeff e (block f A : MvPowerSeries (Var n) ℚ) ≠ 0) :
    e (.y v) = 0 := by
  classical
  change MvPolynomial.coeff e (block f A) ≠ 0 at hn
  rw [block, MvPolynomial.coeff_sum] at hn
  obtain ⟨R,hR,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have he : Finsupp.single Var.w (f R) + yMono R = e := by
    by_contra hx
    simp [term, MvPolynomial.coeff_monomial, hx, Ne.symm hx] at hne
  have hvR : v ∉ R := fun h => hv (Finset.mem_powerset.mp hR h)
  simp [←he,Finsupp.single_apply,ymono_apply,hvR]

lemma block_empty {n : ℕ} (f : Finset (Fin n) → ℕ) (h0 : f ∅=0) : block f ∅ = 1 := by
  classical
  simp [block, term, h0, yMono]

end CutFactors

open scoped Classical BigOperators
open SingleExpBisect.Main
namespace CutFactors
open MvPowerSeries
private def supportedOn {σ : Type} (P : (σ →₀ ℕ) → Prop) (F : MvPowerSeries σ ℚ) : Prop :=
  ∀ m, MvPowerSeries.coeff m F ≠ 0 → P m

private lemma supported_one {σ : Type} {P : (σ →₀ ℕ) → Prop} (h0 : P 0) :
    supportedOn P 1 := by
  classical
  intro m hm
  by_cases he : m = 0
  · simpa [he] using h0
  · simp [MvPowerSeries.coeff_one, he] at hm

private lemma supported_mul {σ : Type} {P : (σ →₀ ℕ) → Prop}
    (hadd : ∀ x y, P x → P y → P (x+y)) {F H : MvPowerSeries σ ℚ}
    (hf : supportedOn P F) (hh : supportedOn P H) : supportedOn P (F*H) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_mul] at hm
  obtain ⟨⟨i,j⟩,hij,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij]
  exact hadd i j (hf i (left_ne_zero_of_mul hn)) (hh j (right_ne_zero_of_mul hn))

private lemma supported_pow {σ : Type} {P : (σ →₀ ℕ) → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x+y)) {F : MvPowerSeries σ ℚ}
    (hf : supportedOn P F) (j : ℕ) : supportedOn P (F^j) := by
  induction j with
  | zero => simpa using supported_one h0
  | succ j ih => rw [pow_succ]; exact supported_mul hadd ih hf

private lemma supported_log {σ : Type} {P : (σ →₀ ℕ) → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x+y)) {F : MvPowerSeries σ ℚ}
    (hf : supportedOn P F) : supportedOn P (logPS F) := by
  classical
  intro m hm
  change (∑ j ∈ Finset.Icc 1 (Finsupp.degree m), ((-1 : ℚ) ^ (j+1) / (j:ℚ)) *
    MvPowerSeries.coeff m ((F-1)^j)) ≠ 0 at hm
  obtain ⟨j,hj,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  apply supported_pow h0 hadd (F := F-1) _ j m (right_ne_zero_of_mul hn)
  intro e he
  by_cases heq : e=0
  · simpa only [heq] using h0
  · apply hf e
    simpa [MvPowerSeries.coeff_one,heq] using he


private lemma restricted_log {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (k : ℕ) (e : Var n →₀ ℕ) (hk : e .w ≤ k) :
    coeff e (logPS (Zfull G W k : MvPowerSeries (Var n) ℚ)) =
    coeff e (logPS (block (mu G W) (W.filter fun v => 0 < e (.y v)) : MvPowerSeries (Var n) ℚ)) := by
  classical
  let U : Set (Var n →₀ ℕ) := {m | ¬ m ≤ e}
  have hU : IsUpClosed U := by
    intro m hm a ha
    exact hm ((show m ≤ m+a from le_self_add).trans ha)
  apply ExpLogProof.logPS_congr_off U hU
  · intro m hm
    exact restricted_coeff G W k e m (not_not.mp hm) hk
  · exact fun h => h le_rfl

private lemma block_log_absent {n : ℕ} (f : Finset (Fin n) → ℕ)
    (A : Finset (Fin n)) (v : Fin n) (hv : v ∉ A) (e : Var n →₀ ℕ) (he : 0 < e (.y v)) :
    coeff e (logPS (block f A : MvPowerSeries (Var n) ℚ)) = 0 := by
  by_contra hn
  have hh : supportedOn (fun m => m (.y v) = 0) (block f A : MvPowerSeries (Var n) ℚ) :=
    block_support f A v hv
  have hval := supported_log (P := fun m => m (.y v) = 0) (by simp)
    (fun x y hx hy => by simp [hx,hy]) hh e hn
  exact (Nat.ne_of_gt he) hval

lemma split_vanish {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n))
    (k : ℕ) (e : Var n →₀ ℕ) (hk : e .w ≤ k) (h0 : mu G W ∅ = 0)
    (hS : A ∪ B = W.filter (fun v => 0 < e (.y v)))
    (ha : A.Nonempty) (hb : B.Nonempty) (hd : Disjoint A B)
    (hadd : ∀ R ⊆ A ∪ B, mu G W R = mu G W (R ∩ A) + mu G W (R ∩ B)) :
    coeff e (logPS (Zfull G W k : MvPowerSeries (Var n) ℚ)) = 0 := by
  classical
  rw [restricted_log G W k e hk, ←hS, block_mul _ A B hd hadd, MvPolynomial.coe_mul,
     ExpLogProof.logPS_mul _ _ (block_const _ h0 A) (block_const _ h0 B), map_add]
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  have heA := (Finset.mem_filter.mp (hS ▸ Finset.mem_union_left B ha)).2
  have heB := (Finset.mem_filter.mp (hS ▸ Finset.mem_union_right A hb)).2
  rw [block_log_absent _ A b (fun h => Finset.disjoint_left.mp hd h hb) e heB,
    block_log_absent _ B a (Finset.disjoint_left.mp hd ha) e heA, add_zero]

lemma empty_vanish {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (k : ℕ)
    (e : Var n →₀ ℕ) (hk : e .w ≤ k) (h0 : mu G W ∅ = 0)
    (hS : W.filter (fun v => 0 < e (.y v)) = ∅) :
    coeff e (logPS (Zfull G W k : MvPowerSeries (Var n) ℚ)) = 0 := by
  classical
  rw [restricted_log G W k e hk, hS]
  rw [block_empty _ h0, MvPolynomial.coe_one]
  change (∑ j ∈ Finset.Icc 1 e.degree, _ * coeff e (((1 : MvPowerSeries (Var n) ℚ)-1)^j)) = 0
  apply Finset.sum_eq_zero
  intro j hj
  have hn : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  simp [zero_pow hn]

end CutFactors

private lemma mem_cutEdges_mk {n : ℕ} (H : SimpleGraph (Fin n)) (X : Finset (Fin n)) (a b : Fin n) :
    s(a, b) ∈ cutEdges H X ↔ H.Adj a b ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)) := by
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeSet,
    Sym2.eq_iff]
  constructor
  · rintro ⟨hadj, u, hu, v, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨hadj, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨hadj, Or.inr ⟨hu, hv⟩⟩
  · rintro ⟨hadj, (⟨ha, hb⟩ | ⟨hb, ha⟩)⟩
    · exact ⟨hadj, a, ha, b, hb, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hadj, b, hb, a, ha, Or.inr ⟨rfl, rfl⟩⟩

/-- Submodularity of the cut function. -/
private lemma cut_submod {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) :
    cutSize G (X ∪ Y) + cutSize G (X ∩ Y) ≤ cutSize G X + cutSize G Y := by
  unfold cutSize
  have h1 : cutEdges G (X ∪ Y) ∪ cutEdges G (X ∩ Y) ⊆ cutEdges G X ∪ cutEdges G Y := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_union, mem_cutEdges_mk, Finset.mem_inter] at he ⊢
      tauto
  have h2 : cutEdges G (X ∪ Y) ∩ cutEdges G (X ∩ Y) ⊆ cutEdges G X ∩ cutEdges G Y := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_union, mem_cutEdges_mk, Finset.mem_inter] at he ⊢
      tauto
  rw [← Finset.card_union_add_card_inter, ← Finset.card_union_add_card_inter (cutEdges G X)]
  exact Nat.add_le_add (Finset.card_le_card h1) (Finset.card_le_card h2)

private lemma mu_le {n : ℕ} (G : SimpleGraph (Fin n)) (W S A : Finset (Fin n)) (h : A ∩ W = S) :
    mu G W S ≤ cutSize G A :=
  Nat.sInf_le ⟨A, h, rfl⟩

private lemma mu_attained {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) (hS : S ⊆ W) :
    ∃ A : Finset (Fin n), A ∩ W = S ∧ cutSize G A = mu G W S :=
  Nat.sInf_mem (s := {c : ℕ | ∃ A : Finset (Fin n), A ∩ W = S ∧ cutSize G A = c})
    ⟨cutSize G S, S, Finset.inter_eq_left.mpr hS, rfl⟩

private lemma mu_subadd {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n))
    (hA : A ⊆ W) (hB : B ⊆ W) :
    mu G W (A ∪ B) ≤ mu G W A + mu G W B := by
  obtain ⟨X,hx,hcut⟩ := mu_attained G W A hA
  obtain ⟨Y,hy,hcut'⟩ := mu_attained G W B hB
  have e : (X ∪ Y) ∩ W = A ∪ B := by rw [Finset.union_inter_distrib_right,hx,hy]
  have hu := mu_le G W _ (X ∪ Y) e
  have hh := cut_submod G X Y
  omega

private def supportedOn {σ : Type} (P : (σ →₀ ℕ) → Prop) (F : MvPowerSeries σ ℚ) : Prop :=
  ∀ m, MvPowerSeries.coeff m F ≠ 0 → P m

private lemma supported_one {σ : Type} {P : (σ →₀ ℕ) → Prop} (h0 : P 0) :
    supportedOn P 1 := by
  classical
  intro m hm
  by_cases he : m = 0
  · simpa [he] using h0
  · simp [MvPowerSeries.coeff_one, he] at hm

private lemma supported_mul {σ : Type} {P : (σ →₀ ℕ) → Prop}
    (hadd : ∀ x y, P x → P y → P (x+y)) {F H : MvPowerSeries σ ℚ}
    (hf : supportedOn P F) (hh : supportedOn P H) : supportedOn P (F*H) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_mul] at hm
  obtain ⟨⟨i,j⟩,hij,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij]
  exact hadd i j (hf i (left_ne_zero_of_mul hn)) (hh j (right_ne_zero_of_mul hn))

private lemma supported_pow {σ : Type} {P : (σ →₀ ℕ) → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x+y)) {F : MvPowerSeries σ ℚ}
    (hf : supportedOn P F) (j : ℕ) : supportedOn P (F^j) := by
  induction j with
  | zero => simpa using supported_one h0
  | succ j ih => rw [pow_succ]; exact supported_mul hadd ih hf

private lemma supported_log {σ : Type} {P : (σ →₀ ℕ) → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x+y)) {F : MvPowerSeries σ ℚ}
    (hf : supportedOn P F) : supportedOn P (logPS F) := by
  classical
  intro m hm
  change (∑ j ∈ Finset.Icc 1 (Finsupp.degree m), ((-1 : ℚ) ^ (j+1) / (j:ℚ)) *
    MvPowerSeries.coeff m ((F-1)^j)) ≠ 0 at hm
  obtain ⟨j,hj,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  apply supported_pow h0 hadd (F := F-1) _ j m (right_ne_zero_of_mul hn)
  intro e he
  by_cases heq : e=0
  · simpa only [heq] using h0
  · apply hf e
    simpa [MvPowerSeries.coeff_one,heq] using he

private lemma mu_empty {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) :
    mu G W ∅ = 0 := by
  have h := mu_le G W ∅ ∅ (Finset.empty_inter _)
  simpa [cutSize,cutEdges] using h

private def suppW {n : ℕ} (W : Finset (Fin n)) (e : Var n →₀ ℕ) :=
  W.filter fun v => 0 < e (Var.y v)

private lemma exponent_recovers {n : ℕ} (W A : Finset (Fin n)) (ha : A ⊆ W) (c : ℕ) :
    suppW W (Finsupp.single Var.w c + yMono A) = A ∧
      (Finsupp.single Var.w c + yMono A : Var n →₀ ℕ) Var.w = c := by
  classical
  constructor
  · ext v
    have hi : (yMono A) (Var.y v) = if v ∈ A then 1 else 0 := by
      simp [yMono,Finsupp.finsetSum_apply,Finsupp.single_apply,eq_comm]
    by_cases hv : v ∈ A
    · simp [suppW,hi,hv,ha hv,Finsupp.single_apply]
    · simp [suppW,hi,hv,Finsupp.single_apply]
  · simp [yMono,Finsupp.finsetSum_apply,Finsupp.single_apply]

private lemma z_supported {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (k : ℕ) :
    supportedOn (fun e => mu G W (suppW W e) ≤ e Var.w) (Zfull G W k : MvPowerSeries (Var n) ℚ) := by
  classical
  intro m hm
  change (MvPolynomial.coeff m (Zfull G W k)) ≠ 0 at hm
  rw [Zfull, MvPolynomial.coeff_sum] at hm
  obtain ⟨A,hA,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hma : Finsupp.single Var.w (mu G W A) + yMono A = m := by
    by_contra hx; simp [MvPolynomial.coeff_monomial,hx,Ne.symm hx] at hn
  rw [←hma]
  obtain ⟨hsp,hw⟩ := exponent_recovers W A (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1) (mu G W A)
  rw [hsp,hw]

private lemma logBound {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (k : ℕ) :
    supportedOn (fun e => mu G W (suppW W e) ≤ e Var.w)
      (logPS (Zfull G W k : MvPowerSeries (Var n) ℚ)) := by
  apply supported_log _ _ (z_supported G W k)
  · simp [suppW,mu_empty]
  · intro e f he hf
    have hu : suppW W (e+f) = suppW W e ∪ suppW W f := by
      ext v; simp only [suppW, Finset.mem_filter, Finset.mem_union]
      change (v ∈ W ∧ 0 < e (Var.y v) + f (Var.y v)) ↔ _
      rw [Nat.add_pos_iff_pos_or_pos]; tauto
    rw [hu]
    exact (mu_subadd G W _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _)).trans
      (Nat.add_le_add he hf)

private lemma remove_closed {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {X K : Finset (Fin n)} (hK : K ⊆ X) (hnK : K.Nonempty)
    (hcl : ∀ {u v}, u ∈ K → v ∈ X → G.Adj u v → v ∈ K)
    (hproper : ∃ v, v ∉ K) :
    cutSize G (X \ K) < cutSize G X := by
  classical
  obtain ⟨z,hz⟩ := hnK
  obtain ⟨w,hw⟩ := hproper
  obtain ⟨p⟩ := hG z w
  obtain ⟨e,he,heu,hev⟩ := p.exists_boundary_dart (K : Set _) hz hw
  have hout : e.snd ∉ X := fun hv => hev (hcl heu hv e.adj)
  have hsub : cutEdges G (X \ K) ⊆ cutEdges G X := by
    intro edge
    induction edge using Sym2.ind with
    | _ a b =>
      simp only [mem_cutEdges_mk, Finset.mem_sdiff]
      intro ⟨ha, hed⟩
      refine ⟨ha, ?_⟩
      by_cases ax : a ∈ X <;> by_cases bx : b ∈ X <;> try tauto
  have huse : s(e.fst, e.snd) ∈ cutEdges G X :=
    (mem_cutEdges_mk ..).mpr ⟨e.adj, Or.inl ⟨hK heu, hout⟩⟩
  have hno : s(e.fst, e.snd) ∉ cutEdges G (X \ K) := by
    simp only [mem_cutEdges_mk, Finset.mem_sdiff]
    tauto
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hno (heq ▸ huse)⟩)

private lemma split_cut {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (hd : Disjoint A B) (hc : ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v) :
    cutSize G (A ∪ B) = cutSize G A + cutSize G B := by
  classical
  have eq : cutEdges G (A ∪ B) = cutEdges G A ∪ cutEdges G B := by
    ext e; induction e using Sym2.ind with
    | _ u v =>
      simp only [mem_cutEdges_mk, Finset.mem_union]
      have h1 := hc u
      have h2 := hc v
      have h3 : G.Adj u v → G.Adj v u := SimpleGraph.Adj.symm
      by_cases h : G.Adj u v
      · have e1 : u ∈ A → v ∉ B := fun hA hB => h1 hA v hB h
        have e2 : v ∈ A → u ∉ B := fun hA hB => h2 hA u hB h.symm
        tauto
      · tauto
  have hdis : Disjoint (cutEdges G A) (cutEdges G B) := by
    apply Finset.disjoint_left.mpr
    intro e h1 h2
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨ha,ho⟩ := (mem_cutEdges_mk ..).mp h1
      obtain ⟨_,hp⟩ := (mem_cutEdges_mk ..).mp h2
      have e1 : u ∈ A → v ∉ B := fun hu hv => hc u hu v hv ha
      have e2 : v ∈ A → u ∉ B := fun hv hu => hc v hv u hu ha.symm
      have e3 : u ∈ A → u ∉ B := fun h => Finset.disjoint_left.mp hd h
      have e4 : v ∈ A → v ∉ B := fun h => Finset.disjoint_left.mp hd h
      tauto
  unfold cutSize; rw [eq, Finset.card_union_of_disjoint hdis]

set_option maxHeartbeats 1400000 in
private lemma phi_split {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (W S : Finset (Fin n)) (hs : S ⊆ W) (hne : S.Nonempty)
    (hdisc : ¬ (G.induce (Phi G W S : Set (Fin n))).Connected) :
    ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = S ∧
      ∀ R ⊆ S, mu G W R = mu G W (R ∩ A) + mu G W (R ∩ B) := by
  classical
  let X := Phi G W S
  let H := G.induce (X : Set (Fin n))
  have hm : X ∩ W = S ∧ cutSize G X = mu G W S := (lemma_3_7 G W S hs).1
  have hsx : S ⊆ X := hm.1 ▸ Finset.inter_subset_left
  obtain ⟨v,hv⟩ := hne
  haveI : Nonempty (X : Set (Fin n)) := ⟨⟨v,hsx hv⟩⟩
  have hpre : ¬ H.Preconnected := fun hh => hdisc (@SimpleGraph.Connected.mk _ H hh inferInstance)
  change ¬ ∀ u v, H.Reachable u v at hpre
  push_neg at hpre
  obtain ⟨p,q,hpq⟩ := hpre
  let K := X.filter fun v => ∃ h : v ∈ X, H.Reachable p ⟨v,h⟩
  let J := X \ K
  have hkx : K ⊆ X := Finset.filter_subset _ _
  have hjx : J ⊆ X := Finset.sdiff_subset
  have hp : p.val ∈ K := Finset.mem_filter.mpr ⟨p.property,p.property,SimpleGraph.Reachable.refl _⟩
  have hq : q.val ∈ J := Finset.mem_sdiff.mpr ⟨q.property,fun h => by
    obtain ⟨_,h'⟩ := (Finset.mem_filter.mp h).2
    exact hpq h'⟩
  have hcl {u v : Fin n} (hu : u ∈ K) (hv : v ∈ X) (ha : G.Adj u v) : v ∈ K := by
    obtain ⟨hu',h⟩ := (Finset.mem_filter.mp hu).2
    have he : H.Adj ⟨u,hu'⟩ ⟨v,hv⟩ := ha
    exact Finset.mem_filter.mpr ⟨hv,hv,h.trans he.reachable⟩
  have hjcl {u v : Fin n} (hu : u ∈ J) (hv : v ∈ X) (ha : G.Adj u v) : v ∈ J :=
    Finset.mem_sdiff.mpr ⟨hv,fun h => (Finset.mem_sdiff.mp hu).2 (hcl h (hjx hu) ha.symm)⟩
  have hit (D : Finset (Fin n)) (hdx : D ⊆ X) (hd : D.Nonempty) (ho : ∃ v, v ∉ D)
      (hclosed : ∀ {u v}, u ∈ D → v ∈ X → G.Adj u v → v ∈ D) : (S ∩ D).Nonempty := by
    by_contra hno
    have same : (X \ D) ∩ W = S := by
      rw [←hm.1]; ext u; simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · tauto
      · intro hh; exact ⟨⟨hh.1,fun hd' => hno ⟨u,Finset.mem_inter.mpr ⟨hm.1 ▸ Finset.mem_inter.mpr hh,hd'⟩⟩⟩,hh.2⟩
    have hcut := remove_closed hG hdx hd hclosed ho
    have hlow := mu_le G W S (X \ D) same
    omega
  have dj : Disjoint K J := Finset.disjoint_left.mpr (fun _ hk hj => (Finset.mem_sdiff.mp hj).2 hk)
  have du (R : Finset (Fin n)) (hR : R ⊆ X) : (R ∩ K) ∪ (R ∩ J) = R := by
    ext v; simp only [J,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]; by_cases h : v ∈ K <;> aesop
  refine ⟨S ∩ K,S ∩ J,hit K hkx ⟨_,hp⟩ ⟨_,(Finset.mem_sdiff.mp hq).2⟩ hcl,
    hit J hjx ⟨_,hq⟩ ⟨_,Finset.disjoint_left.mp dj hp⟩ hjcl,
    dj.mono Finset.inter_subset_right Finset.inter_subset_right,du S hsx,?_⟩
  intro R hR
  have hre (D : Finset (Fin n)) : R ∩ (S ∩ D) = R ∩ D := by
    ext x; simp only [Finset.mem_inter]; constructor <;> aesop
  simp only [hre]
  let Y := Phi G W R
  have hy : Y ∩ W = R ∧ cutSize G Y = mu G W R := (lemma_3_7 G W R (hR.trans hs)).1
  have hyx : Y ⊆ X := lemma_3_8 G W R S hR hs
  have hcut := split_cut G (Y ∩ K) (Y ∩ J) (dj.mono Finset.inter_subset_right Finset.inter_subset_right)
    (fun _ hu _ hv ha => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).2
      (hcl (Finset.mem_inter.mp hu).2 (hyx (Finset.mem_inter.mp hv).1) ha))
  rw [du Y hyx,hy.2] at hcut
  have part (D : Finset (Fin n)) : mu G W (R ∩ D) ≤ cutSize G (Y ∩ D) := by
    exact mu_le G W (R ∩ D) (Y ∩ D) ((Finset.inter_right_comm Y D W).trans
      (congrArg (fun Z => Z ∩ D) hy.1))
  have hh := mu_subadd G W (R ∩ K) (R ∩ J) (Finset.inter_subset_left.trans (hR.trans hs))
    (Finset.inter_subset_left.trans (hR.trans hs))
  rw [du R (hR.trans hsx)] at hh
  have h1 := part K
  have h2 := part J
  omega

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (T : RootedTD n) (k : ℕ)
    (hT : IsSec3Decomp G T k) (t : Fin T.N) (c : ℕ) (hc : c ≤ k) (a : Fin n → ℕ)
    (hcoeff : MvPowerSeries.coeff
      (Finsupp.single Var.w c + ∑ v ∈ T.cone t, Finsupp.single (Var.y v) (a v))
      (logPS (Zfull G (T.cone t) k : MvPowerSeries (Var n) ℚ)) ≠ 0) :
    (G.induce (Phi G (T.cone t) ((T.cone t).filter (fun v => 0 < a v)) : Set (Fin n))).Connected ∧
      cutSize G (Phi G (T.cone t) ((T.cone t).filter (fun v => 0 < a v))) ≤ c := by
  classical
  let W := T.cone t
  let e := Finsupp.single Var.w c + ∑ v ∈ W, Finsupp.single (Var.y v) (a v)
  let S := W.filter (fun v => 0 < a v)
  have hw : e Var.w = c := by simp [e,Finsupp.finsetSum_apply,Finsupp.single_apply]
  have hsup : W.filter (fun v => 0 < e (Var.y v)) = S := by
    ext v
    simp only [S,Finset.mem_filter]
    by_cases hv : v ∈ W
    · simp [hv,e,Finsupp.finsetSum_apply,Finsupp.single_apply,eq_comm]
    · simp [hv]
  have hne : S.Nonempty := by
    by_contra h
    have hem : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    exact hcoeff (CutFactors.empty_vanish G W k e (hw.le.trans hc) (mu_empty G W) (hsup.trans hem))
  constructor
  · by_contra h
    obtain ⟨A,B,ha,hb,hd,hu,hadd⟩ := phi_split G hG W S (Finset.filter_subset _ _) hne h
    exact hcoeff (CutFactors.split_vanish G W A B k e (hw.le.trans hc) (mu_empty G W)
      (hu.trans hsup.symm) ha hb hd (fun R hR => hadd R (hu ▸ hR)))
  · have h := logBound G W k e hcoeff
    change mu G W (W.filter (fun v => 0 < e (.y v))) ≤ e .w at h
    rw [hsup,hw] at h
    exact ((lemma_3_7 G W S (Finset.filter_subset _ _)).1.2).le.trans h

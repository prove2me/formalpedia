-- Prove2me | solution 1 for RLCDiscrepancy.lemma_4_13_of_ten_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:17:39.093032+00:00
-- url     : https://prove2.me/submissions/a6c3df64-5719-4f74-8018-c38d98bab248

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_RLCDiscrepancy_capacity
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_consSeq
import Definitions.Def_RLCDiscrepancy_IsSmooth
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_RLCDiscrepancy_smoothLambda
import Definitions.Def_RLCDiscrepancy_IsMonotone
import Theorems.Thm_RLCDiscrepancy_lemma_4_12

section
set_option autoImplicit false
open Classical

namespace RLCDiscrepancy.Dev.L413bProd

variable {V : Type*} [Fintype V] [Zero V] {k : ℕ}

/-- Splitting off one coordinate. -/
def splitEquiv (a : Fin k) : (Fin k → V) ≃ V × {w : Fin k → V // w a = 0}
    where
  toFun := fun u => ⟨u a, ⟨Function.update u a 0, by simp⟩⟩
  invFun := fun p => Function.update p.2.1 a p.1
  left_inv := by
    intro u; simp
  right_inv := by
    rintro ⟨v, w, hw⟩
    simp [Function.update_idem, hw]

lemma card_split (a : Fin k) (P : (Fin k → V) → Prop) [DecidablePred P] :
    ((Finset.univ.filter P).card : ℝ) =
      ∑ w : {w : Fin k → V // w a = 0},
        ((Finset.univ.filter (fun v : V => P (Function.update w.1 a v))).card : ℝ) := by
  have h1 : ((Finset.univ.filter P).card : ℝ) = ∑ u : Fin k → V, if P u then (1:ℝ) else 0 := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [h1, ← (splitEquiv (V := V) a).symm.sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.card_filter]; push_cast
  rfl

/-- Product-structure counting inequality. -/
theorem card_forall_le (G : Fin k → (Fin k → V) → Prop) (p : ℝ) (hp0 : 0 ≤ p)
    (hdep : ∀ (j : Fin k) (u u' : Fin k → V), (∀ i, i ≤ j → u i = u' i) → (G j u ↔ G j u'))
    (hp : ∀ (j : Fin k) (u : Fin k → V),
      ((Finset.univ.filter (fun v : V => G j (Function.update u j v))).card : ℝ) ≤
        p * Fintype.card V)
    (S : Finset (Fin k)) :
    ((Finset.univ.filter (fun u : Fin k → V => ∀ j ∈ S, G j u)).card : ℝ) ≤
      p ^ S.card * (Fintype.card V : ℝ) ^ k := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have hind : ∀ (w : Fin k → V) (v : V) (j : Fin k), j ∈ s →
        (G j (Function.update w a v) ↔ G j w) := by
      intro w v j hj
      apply hdep
      intro i hi
      have : i ≠ a := ne_of_lt (lt_of_le_of_lt hi (hlt j hj))
      simp [Function.update_of_ne this]
    set X : (Fin k → V) → Prop := fun u => ∀ j ∈ s, G j u with hX
    have hXind : ∀ (w : Fin k → V) (v : V), X (Function.update w a v) ↔ X w := by
      intro w v
      simp only [hX]
      exact forall₂_congr (fun j hj => hind w v j hj)
    have e1 : ((Finset.univ.filter (fun u : Fin k → V => ∀ j ∈ insert a s, G j u)).card : ℝ) =
        ∑ w : {w : Fin k → V // w a = 0},
          ((Finset.univ.filter (fun v : V => ∀ j ∈ insert a s, G j (Function.update w.1 a v))).card : ℝ) :=
      by convert card_split a (fun u => ∀ j ∈ insert a s, G j u)
    have e2 : ((Finset.univ.filter X).card : ℝ) =
        ∑ w : {w : Fin k → V // w a = 0},
          ((Finset.univ.filter (fun v : V => X (Function.update w.1 a v))).card : ℝ) :=
      by convert card_split a X
    have e3 : ∀ w : {w : Fin k → V // w a = 0},
        ((Finset.univ.filter (fun v : V => ∀ j ∈ insert a s, G j (Function.update w.1 a v))).card : ℝ)
          ≤ p * ((Finset.univ.filter (fun v : V => X (Function.update w.1 a v))).card : ℝ) := by
      intro w
      by_cases hw : X w.1
      · have h4 : (Finset.univ.filter (fun v : V => X (Function.update w.1 a v))) = Finset.univ := by
          ext v; simp [(hXind w.1 v).2 hw]
        rw [h4]
        have h5 : (Finset.univ.filter (fun v : V => ∀ j ∈ insert a s, G j (Function.update w.1 a v)))
            ⊆ Finset.univ.filter (fun v : V => G a (Function.update w.1 a v)) := by
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          exact hv a (Finset.mem_insert_self _ _)
        have h6 := Finset.card_le_card h5
        have h7 := hp a w.1
        have h8 : (Finset.univ.filter (fun v : V => G a (Function.update w.1 a v))).card ≤ _ := le_rfl
        simp only [Finset.card_univ]
        calc _ ≤ ((Finset.univ.filter (fun v : V => G a (Function.update w.1 a v))).card : ℝ) := by
              exact_mod_cast h6
          _ ≤ _ := h7
      · have h4 : (Finset.univ.filter (fun v : V => ∀ j ∈ insert a s, G j (Function.update w.1 a v))) = ∅ := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hv
          exact hw ((hXind w.1 v).1 (fun j hj => hv j (Finset.mem_insert_of_mem hj)))
        rw [h4]
        simp only [Finset.card_empty, Nat.cast_zero]
        positivity
    calc _ ≤ ∑ w : {w : Fin k → V // w a = 0},
          p * ((Finset.univ.filter (fun v : V => X (Function.update w.1 a v))).card : ℝ) := by
          rw [e1]; exact Finset.sum_le_sum fun w _ => e3 w
      _ = p * ((Finset.univ.filter X).card : ℝ) := by rw [e2, Finset.mul_sum]
      _ ≤ p * (p ^ s.card * (Fintype.card V : ℝ) ^ k) := mul_le_mul_of_nonneg_left ih hp0
      _ = _ := by rw [Finset.card_insert_of_notMem has]; ring

end RLCDiscrepancy.Dev.L413bProd
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Classical

namespace RLCDiscrepancy.Dev.L413b
open RLCDiscrepancy RLCDiscrepancy.Dev.L413bProd

variable {F : Type*} [Field F] [Fintype F] {n k : ℕ} {f : (Fin n → F) → ℝ}

noncomputable def dv (u : Fin k → Fin n → F) (f : (Fin n → F) → ℝ) (i : ℕ) : ℝ :=
  |relDev (consSeq u i) f|

noncomputable def rho (q : ℝ) (k : ℕ) : ℝ := (1 + 1 / (k : ℝ)) / q

/-- first half of "step j+1 is bad": the deviation before the step is large -/
def badPre (f : (Fin n → F) → ℝ) (Γ t : ℝ) (u : Fin k → Fin n → F) (j : ℕ) : Prop :=
  ((Fintype.card F : ℝ) ^ k * smoothLambda f k Γ) *
      rho (Fintype.card F) k ^ (((j : ℝ) + 1) - t / 2) < dv u f j

def badStep (f : (Fin n → F) → ℝ) (Γ t : ℝ) (u : Fin k → Fin n → F) (j : ℕ) : Prop :=
  badPre f Γ t u j ∧ rho (Fintype.card F) k * dv u f j < dv u f (j + 1)

def tPre (f : (Fin n → F) → ℝ) (Γ : ℝ) (u : Fin k → Fin n → F) (j : ℕ) : Prop :=
  |relDev (consSeq u j) (selfConv f)| ≤ (Fintype.card F : ℝ) ^ (k - j) * Γ

def GG (f : (Fin n → F) → ℝ) (Γ t : ℝ) (u : Fin k → Fin n → F) (j : Fin k) : Prop :=
  tPre f Γ u j ∧ badStep f Γ t u j

/-! ## elementary facts -/

lemma two_le_card : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by
  have : 1 < Fintype.card F := Fintype.one_lt_card
  exact_mod_cast this

lemma le_sup (x : Fin n → F) : f x ≤ supNorm f :=
  (le_abs_self _).trans (Finset.le_sup' (fun x => |f x|) (Finset.mem_univ x))

lemma sup_ge_one (hf : IsNormalized f) : 1 ≤ supNorm f := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => le_sup (f := f) x)
  rw [hf.2] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_fin] at h
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ n := by
    have := two_le_card (F := F); positivity
  push_cast at h
  by_contra hlt
  have hlt := not_le.1 hlt
  nlinarith

lemma dv_le_sup (hf : IsNormalized f) (u : Fin k → Fin n → F) (i : ℕ) :
    dv u f i ≤ supNorm f := by
  unfold dv relDev
  set C := consSeq u i
  have hcard : (0 : ℝ) < (codeFinset C).card := by
    have : (0 : Fin n → F) ∈ codeFinset C := by simp
    exact_mod_cast Finset.card_pos.2 ⟨_, this⟩
  have h1 : (∑ x ∈ codeFinset C, f x) ≤ (codeFinset C).card * supNorm f := by
    have := Finset.sum_le_sum (fun x (_ : x ∈ codeFinset C) => le_sup (f := f) x)
    simpa using this
  have h2 : 0 ≤ ∑ x ∈ codeFinset C, f x := Finset.sum_nonneg fun x _ => hf.1 x
  have h3 : (∑ x ∈ codeFinset C, f x) / (codeFinset C).card ≤ supNorm f := by
    rw [div_le_iff₀ hcard]; linarith
  have h4 : 0 ≤ (∑ x ∈ codeFinset C, f x) / (codeFinset C).card := div_nonneg h2 hcard.le
  have h5 := sup_ge_one hf
  rw [abs_le]; constructor <;> linarith

lemma sup_le_A (Γ : ℝ) (f : (Fin n → F) → ℝ) :
    supNorm f ≤ (Fintype.card F : ℝ) ^ k * smoothLambda f k Γ := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) ^ k := by
    have := two_le_card (F := F); positivity
  have h : supNorm f * ((Fintype.card F : ℝ) ^ k)⁻¹ ≤ smoothLambda f k Γ := le_max_left _ _
  rw [← div_eq_mul_inv, div_le_iff₀ hq] at h
  linarith

lemma Lam_pos (Γ : ℝ) (hΓ : 0 < Γ) (f : (Fin n → F) → ℝ) : 0 < smoothLambda f k Γ :=
  lt_of_lt_of_le (Real.sqrt_pos.2 hΓ) (le_max_right _ _)

/-! ## the deterministic part -/

lemma induct_claim (d : ℕ → ℝ) (A ρ t : ℝ) (hA : 0 ≤ A) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ht : 0 ≤ t) (h0 : d 0 ≤ A) (ℓ : ℕ) (hmono : ∀ j, j < ℓ → d (j + 1) ≤ d j) :
    ∀ i, i ≤ ℓ → d i ≤ A * ρ ^ (((i : ℝ) -
      (((Finset.range i).filter (fun j : ℕ => A * ρ ^ (((j : ℝ) + 1) - t / 2) < d j ∧
        ρ * d j < d (j + 1))).card : ℝ)) - t / 2) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      sub_zero, zero_sub]
    have : 1 ≤ ρ ^ (-(t / 2)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ0 hρ1 (by linarith)
    nlinarith
  | succ i ih =>
    intro hi
    have ih := ih (by omega)
    have hm := hmono i (by omega)
    set cnt := ((Finset.range i).filter (fun j : ℕ => A * ρ ^ (((j : ℝ) + 1) - t / 2) < d j ∧
        ρ * d j < d (j + 1))).card with hcnt
    have hrec : ((Finset.range (i + 1)).filter (fun j : ℕ => A * ρ ^ (((j : ℝ) + 1) - t / 2) < d j ∧
        ρ * d j < d (j + 1))).card =
        cnt + (if (A * ρ ^ (((i : ℝ) + 1) - t / 2) < d i ∧ ρ * d i < d (i + 1)) then 1 else 0) := by
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hb : (A * ρ ^ (((i : ℝ) + 1) - t / 2) < d i ∧ ρ * d i < d (i + 1))
      · rw [if_pos hb, if_pos hb, Finset.card_insert_of_notMem (by simp)]
      · rw [if_neg hb, if_neg hb]; simp [hcnt]
    rw [hrec]
    by_cases hb : (A * ρ ^ (((i : ℝ) + 1) - t / 2) < d i ∧ ρ * d i < d (i + 1))
    · rw [if_pos hb]
      have : (((i + 1 : ℕ) : ℝ) - ((cnt + 1 : ℕ) : ℝ)) - t / 2 = ((i : ℝ) - cnt) - t / 2 := by
        push_cast; ring
      rw [this]; exact hm.trans ih
    · rw [if_neg hb]
      have e' : (((i + 1 : ℕ) : ℝ) - ((cnt + 0 : ℕ) : ℝ)) - t / 2 = (((i : ℝ) - cnt) - t / 2) + 1 := by
        push_cast; ring
      rw [e']
      by_cases hP : A * ρ ^ (((i : ℝ) + 1) - t / 2) < d i
      · have hQ : d (i + 1) ≤ ρ * d i := by
          by_contra hQ; exact hb ⟨hP, not_le.1 hQ⟩
        rw [Real.rpow_add_one hρ0.ne']
        calc d (i + 1) ≤ ρ * d i := hQ
          _ ≤ ρ * (A * ρ ^ (((i : ℝ) - cnt) - t / 2)) := by gcongr
          _ = _ := by ring
      · have hP' := not_lt.1 hP
        have hcn : (0 : ℝ) ≤ cnt := Nat.cast_nonneg _
        have : ρ ^ (((i : ℝ) + 1) - t / 2) ≤ ρ ^ ((((i : ℝ) - cnt) - t / 2) + 1) :=
          Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by linarith)
        calc d (i + 1) ≤ d i := hm
          _ ≤ A * ρ ^ (((i : ℝ) + 1) - t / 2) := hP'
          _ ≤ _ := by gcongr

lemma count_arith (q : ℝ) (hq : 2 ≤ q) (k ℓ : ℕ) (hk : 10 ≤ k) (hℓ : ℓ ≤ k) (t b : ℝ)
    (ht10 : 10 ≤ t) (hb : 0 ≤ b)
    (h : q ^ t < q ^ ℓ * (((1 + 1 / (k : ℝ)) / q) ^ ((ℓ : ℝ) - b - t / 2))) :
    t / 4 ≤ b := by
  have hq0 : 0 < q := by linarith
  have hk0 : (0 : ℝ) < k := by have : (10:ℝ) ≤ k := by exact_mod_cast hk
                               linarith
  have hk10 : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hρ : 0 < (1 + 1 / (k : ℝ)) / q := by positivity
  have hlog := Real.log_lt_log (by positivity) h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_rpow hρ,
    Real.log_rpow hq0, Real.log_div (by positivity) hq0.ne'] at hlog
  set L := Real.log q with hL
  set m := Real.log (1 + 1 / (k : ℝ)) with hm
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hq
  have hL3 : 0.69 < L := lt_of_lt_of_le (by have := Real.log_two_gt_d9; linarith) hL2
  have hm0 : 0 ≤ m := Real.log_nonneg (by have : 0 < 1 / (k:ℝ) := by positivity
                                          linarith)
  have hm1 : m ≤ 1 / (k : ℝ) := by
    have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (k : ℝ)) (by positivity)
    linarith
  have hℓk : (ℓ : ℝ) ≤ k := by exact_mod_cast hℓ
  have hℓm : (ℓ : ℝ) * m ≤ 1 := by
    calc (ℓ : ℝ) * m ≤ (k : ℝ) * (1 / (k : ℝ)) := by
          apply mul_le_mul hℓk hm1 hm0 hk0.le
      _ = 1 := by field_simp
  have hbm : 0 ≤ b * m := mul_nonneg hb hm0
  have htm : 0 ≤ t * m := mul_nonneg (by linarith) hm0
  by_contra hcon
  have hcon := not_le.1 hcon
  have hbL : b * L < t / 4 * L := by nlinarith
  nlinarith

lemma exists_bad (hf : IsNormalized f) (Γ : ℝ) (hΓ : 0 < Γ) (t : ℝ) (ht10 : 10 ≤ t)
    (htk : t ≤ k) (u : Fin k → Fin n → F)
    (hmono : IsMonotone u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ))
    (hns : ¬ IsSmooth u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) :
    ∃ B : Finset ℕ, (∀ j ∈ B, j < k ∧ badStep f Γ t u j) ∧ t / 4 ≤ (B.card : ℝ) := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq2 : 2 ≤ q := two_le_card
  have hq0 : 0 < q := by linarith
  set Λ := smoothLambda f k Γ with hΛ
  have hΛ0 : 0 < Λ := Lam_pos Γ hΓ f
  have hk10 : 10 ≤ k := by
    have : (10 : ℝ) ≤ k := ht10.trans htk
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by have : (10:ℝ) ≤ k := by exact_mod_cast hk10
                               linarith
  have hqk0 : 0 < q ^ k := by positivity
  have hρ0 : 0 < rho q k := by unfold rho; positivity
  have hρ1 : rho q k ≤ 1 := by
    unfold rho
    rw [div_le_one hq0]
    have : 1 / (k : ℝ) ≤ 1 / 10 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hk10
    linarith
  have hex : ∃ i, i ≤ k ∧ q ^ (k - i) * (q ^ t * Λ) < dv u f i := by
    by_contra hcon
    apply hns
    intro i hi
    by_contra h2
    exact hcon ⟨i, hi, not_le.1 h2⟩
  let ℓ := Nat.find hex
  have hℓ : ℓ ≤ k ∧ q ^ (k - ℓ) * (q ^ t * Λ) < dv u f ℓ := Nat.find_spec hex
  have hmin : ∀ i, i < ℓ → ¬ (i ≤ k ∧ q ^ (k - i) * (q ^ t * Λ) < dv u f i) :=
    fun i hi => Nat.find_min hex hi
  have hmono' : ∀ j, j < ℓ → dv u f (j + 1) ≤ dv u f j := by
    intro j hj
    have hjk : j + 1 ≤ k := by have := hℓ.1; omega
    have := hmono (j + 1) (by omega) hjk (by
      intro i hi
      have hil : i < ℓ := by simp at hi; omega
      have := hmin i hil
      have hik : i ≤ k := by omega
      by_contra hh
      exact this ⟨hik, not_le.1 hh⟩)
    simpa [dv] using this
  have hA0 : 0 ≤ q ^ k * Λ := by positivity
  have h0 : dv u f 0 ≤ q ^ k * Λ := (dv_le_sup hf u 0).trans (sup_le_A Γ f)
  have hind := induct_claim (dv u f) (q ^ k * Λ) (rho q k) t hA0 hρ0 hρ1 (by linarith) h0 ℓ hmono' ℓ le_rfl
  set B := (Finset.range ℓ).filter (fun j => badStep f Γ t u j) with hB
  have hind' : dv u f ℓ ≤ q ^ k * Λ * rho q k ^ (((ℓ : ℝ) - (B.card : ℝ)) - t / 2) := by
    rw [hB]
    convert hind using 7
    ext j
    rw [Finset.mem_filter, Finset.mem_filter]
    exact and_congr_right (fun _ => Iff.rfl)
  have hlt : q ^ (k - ℓ) * (q ^ t * Λ) < q ^ k * Λ * rho q k ^ (((ℓ : ℝ) - (B.card : ℝ)) - t / 2) :=
    lt_of_lt_of_le hℓ.2 hind'
  have hqk : q ^ k = q ^ (k - ℓ) * q ^ ℓ := by rw [← pow_add]; congr 1; omega
  have hc : 0 < q ^ (k - ℓ) * Λ := by positivity
  have h2 : q ^ t < q ^ ℓ * rho q k ^ ((ℓ : ℝ) - (B.card : ℝ) - t / 2) := by
    have h3 : (q ^ (k - ℓ) * Λ) * q ^ t <
        (q ^ (k - ℓ) * Λ) * (q ^ ℓ * rho q k ^ ((ℓ : ℝ) - (B.card : ℝ) - t / 2)) := by
      rw [hqk] at hlt; nlinarith [hlt]
    exact lt_of_mul_lt_mul_left h3 hc.le
  have h4 : t / 4 ≤ (B.card : ℝ) :=
    count_arith q hq2 k ℓ hk10 hℓ.1 t (B.card : ℝ) ht10 (Nat.cast_nonneg _) h2
  refine ⟨B, ?_, h4⟩
  intro j hj
  rw [hB, Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨by have := hℓ.1; omega, hj.2⟩

/-! ## the probabilistic part -/

lemma consSeq_update_lt (u : Fin k → Fin n → F) (j : Fin k) (v : Fin n → F) (i : ℕ)
    (hi : i ≤ j) : consSeq (Function.update u j v) i = consSeq u i := by
  unfold consSeq
  congr 1
  apply Set.image_congr
  intro m hm
  have : m ≠ j := by
    intro h; subst h; simp at hm; omega
  simp [Function.update_of_ne this]

lemma consSeq_update_succ (u : Fin k → Fin n → F) (j : Fin k) (v : Fin n → F) :
    consSeq (Function.update u j v) (j + 1) = consSeq u j ⊔ Submodule.span F {v} := by
  unfold consSeq
  rw [← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    by_cases h : m = j
    · subst h; right; simp
    · left
      refine ⟨m, ?_, by simp [Function.update_of_ne h]⟩
      have : (m : ℕ) ≠ j := fun h' => h (Fin.ext h')
      omega
  · rintro (⟨m, hm, rfl⟩ | rfl)
    · have : m ≠ j := by intro h; subst h; omega
      exact ⟨m, by omega, by simp [Function.update_of_ne this]⟩
    · exact ⟨j, by omega, by simp⟩

lemma GG_dep (f : (Fin n → F) → ℝ) (Γ t : ℝ) (j : Fin k) (u u' : Fin k → Fin n → F)
    (h : ∀ i, i ≤ j → u i = u' i) : GG f Γ t u j ↔ GG f Γ t u' j := by
  have hc : ∀ i : ℕ, i ≤ (j : ℕ) + 1 → consSeq u i = consSeq u' i := by
    intro i hi
    unfold consSeq
    congr 1
    apply Set.image_congr
    intro m hm
    apply h
    simp at hm
    rw [Fin.le_def]; omega
  have h1 := hc j (by omega)
  have h2 := hc (j + 1) le_rfl
  unfold GG tPre badStep badPre dv
  rw [h1, h2]

lemma bound_pre (hf : IsNormalized f) (Γ : ℝ) (hΓ : 0 < Γ) (t : ℝ) (ht10 : 10 ≤ t)
    (htk : t ≤ k) (u : Fin k → Fin n → F) (j : Fin k)
    (hT : tPre f Γ u j) (hB : badPre f Γ t u j) :
    ((Finset.univ.filter (fun v : Fin n → F =>
        rho (Fintype.card F) k * dv u f j <
          |relDev (consSeq u j ⊔ Submodule.span F {v}) f|)).card : ℝ) ≤
      (((Fintype.card F : ℝ) ^ 3 * (k : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ t) *
        (Fintype.card (Fin n → F) : ℝ)) := by
  have hq2 : 2 ≤ (Fintype.card F : ℝ) := two_le_card
  have hΛ0 : 0 < smoothLambda f k Γ := Lam_pos Γ hΓ f
  have hsq : Real.sqrt Γ ≤ smoothLambda f k Γ := le_max_right _ _
  have hsupA := sup_le_A (F := F) (k := k) Γ f
  have hdjsup : dv u f j ≤ (Fintype.card F : ℝ) ^ k * smoothLambda f k Γ :=
    (dv_le_sup hf u j).trans hsupA
  have hN : (0 : ℝ) < (Fintype.card (Fin n → F) : ℝ) := by
    have : 0 < Fintype.card (Fin n → F) := Fintype.card_pos
    exact_mod_cast this
  unfold tPre at hT
  unfold badPre at hB
  have hdvj : dv u f j = |relDev (consSeq u j) f| := rfl
  generalize hC : consSeq u j = C at hT hB hdvj ⊢
  generalize hqdef : (Fintype.card F : ℝ) = q at *
  generalize hΛ : smoothLambda f k Γ = Λ at *
  have hq0 : 0 < q := by linarith
  have hk10 : (10 : ℝ) ≤ k := ht10.trans htk
  have hk0 : (0 : ℝ) < k := by linarith
  generalize hδ : relDev C f = δ at *
  generalize hxx : relDev C (selfConv f) = xx at *
  generalize hdv : dv u f j = dj at *
  have hρdef : rho q k = 1 / q + 1 / (q * k) := by
    unfold rho; field_simp
  have hρ0 : 0 < rho q k := by unfold rho; positivity
  have hρ1 : rho q k ≤ 1 := by
    unfold rho
    rw [div_le_one hq0]
    have : 1 / (k : ℝ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hk10
    linarith
  have hρq : 1 / q ≤ rho q k := by rw [hρdef]; have : 0 < 1 / (q * k) := by positivity
                                   linarith
  have hqt : 0 < q ^ t := Real.rpow_pos_of_pos hq0 t
  have hAsup : |δ| ≤ q ^ k * Λ := hdvj ▸ hdjsup
  rw [hdvj] at hB
  have he : 0 ≤ ((j : ℕ) : ℝ) + 1 - t / 2 := by
    by_contra hneg
    have hneg := not_le.1 hneg
    have h1 : 1 ≤ rho q k ^ (((j : ℕ) : ℝ) + 1 - t / 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ0 hρ1 hneg.le
    have h2 : 0 < q ^ k * Λ := by positivity
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (j : ℕ) + 1 + m := ⟨k - (j + 1), by have := j.2; omega⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = q ^ ((j : ℕ) + 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = q ^ m := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = q ^ (t / 2) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb1 : 1 ≤ b := by rw [hb]; exact one_le_pow₀ (by linarith)
  have hb0 : 0 < b := by linarith
  have hy0 : 0 < y := by rw [hy]; exact Real.rpow_pos_of_pos hq0 _
  have hyy : y * y = q ^ t := by
    rw [hy, ← Real.rpow_add hq0]; congr 1; ring
  have hqk : q ^ k = a * b := by rw [hm, pow_add, ha, hb]
  -- rho^e ≥ y / a
  have hρe : y / a ≤ rho q k ^ (((j : ℕ) : ℝ) + 1 - t / 2) := by
    have h1 : (1 / q) ^ (((j : ℕ) : ℝ) + 1 - t / 2) ≤ rho q k ^ (((j : ℕ) : ℝ) + 1 - t / 2) :=
      Real.rpow_le_rpow (by positivity) hρq he
    refine le_trans (le_of_eq ?_) h1
    rw [one_div, Real.inv_rpow hq0.le, Real.rpow_sub hq0, hy, ha]
    rw [show (((j : ℕ) : ℝ) + 1) = (((j : ℕ) + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [inv_div]
  have hδlow : b * Λ * y < |δ| := by
    have : b * Λ * y ≤ q ^ k * Λ * rho q k ^ (((j : ℕ) : ℝ) + 1 - t / 2) := by
      rw [hqk]
      calc b * Λ * y = a * b * Λ * (y / a) := by field_simp
        _ ≤ _ := by gcongr
    linarith
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hδlow
    have : 0 < b * Λ * y := by positivity
    linarith
  -- apply Lemma 4.12
  have hlam : 0 < 1 / (q * k) := by positivity
  have h412 := lemma_4_12 f hf C (by rw [hδ]; exact hδ0) (1 / (q * k)) hlam
  rw [hδ, hxx, hqdef] at h412
  unfold PunctSketch.coinProb at h412
  have hcardΩ : (Fintype.card (Fin n → F) : ℝ) = (Fintype.card (Fin n → F) : ℝ) := rfl
  -- bound the right-hand side
  have hx : xx ≤ q * b * Λ ^ 2 := by
    have h1 : |xx| ≤ q ^ (k - (j : ℕ)) * Γ := hT
    have h2 : q ^ (k - (j : ℕ)) = q * b := by
      rw [hb, show k - (j : ℕ) = m + 1 by omega, pow_succ]; ring
    have h3 : Γ ≤ Λ ^ 2 := by
      have := Real.sq_sqrt hΓ.le
      have h4 : Real.sqrt Γ ≤ Λ := hsq
      nlinarith [Real.sqrt_nonneg Γ]
    have h5 := (le_abs_self (xx)).trans h1
    rw [h2] at h5
    calc xx ≤ q * b * Γ := h5
      _ ≤ q * b * Λ ^ 2 := by gcongr
  have hc0 : 0 ≤ ((q - 1) / q) ^ 2 := sq_nonneg _
  have hc1 : ((q - 1) / q) ^ 2 ≤ 1 := by
    have h1 : 0 ≤ (q - 1) / q := div_nonneg (by linarith) hq0.le
    have h2 : (q - 1) / q ≤ 1 := by rw [div_le_one hq0]; linarith
    exact pow_le_one₀ h1 h2
  have hnum : ((q - 1) / q) ^ 2 * xx ≤ q * b * Λ ^ 2 := by
    by_cases hxs : xx ≤ 0
    · have : ((q - 1) / q) ^ 2 * xx ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 hxs
      have : 0 ≤ q * b * Λ ^ 2 := by positivity
      linarith
    · have hxs := not_le.1 hxs
      calc ((q - 1) / q) ^ 2 * xx ≤ 1 * xx := by gcongr
        _ ≤ q * b * Λ ^ 2 := by rw [one_mul]; exact hx
  have hden : (1 / (q * k)) ^ 2 * (b * Λ * y) ^ 2 ≤ (1 / (q * k)) ^ 2 * δ ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have : (b * Λ * y) ^ 2 ≤ |δ| ^ 2 := pow_le_pow_left₀ (by positivity) hδlow.le 2
    rwa [sq_abs] at this
  have hden0 : 0 < (1 / (q * k)) ^ 2 * (b * Λ * y) ^ 2 := by positivity
  have hrhs : ((q - 1) / q) ^ 2 * xx /
        ((1 / (q * k)) ^ 2 * δ ^ 2) ≤ q ^ 3 * (k : ℝ) ^ 2 / q ^ t := by
    calc ((q - 1) / q) ^ 2 * xx / ((1 / (q * k)) ^ 2 * δ ^ 2)
        ≤ (q * b * Λ ^ 2) / ((1 / (q * k)) ^ 2 * δ ^ 2) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (q * b * Λ ^ 2) / ((1 / (q * k)) ^ 2 * (b * Λ * y) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hden0 hden
      _ = q / (b * ((1 / (q * k)) ^ 2 * (y * y))) := by field_simp
      _ ≤ q / ((1 / (q * k)) ^ 2 * (y * y)) := by
          have hX : 0 < (1 / (q * k)) ^ 2 * (y * y) := by positivity
          exact div_le_div_of_nonneg_left hq0.le hX (le_mul_of_one_le_left hX.le hb1)
      _ = q ^ 3 * (k : ℝ) ^ 2 / q ^ t := by rw [hyy]; field_simp
  have h412' := h412.trans hrhs
  rw [div_le_iff₀ hN] at h412'
  refine le_trans (le_of_eq ?_) h412'
  congr 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hρdef, hdvj, mul_comm]

lemma step_bound (hf : IsNormalized f) (Γ : ℝ) (hΓ : 0 < Γ) (t : ℝ) (ht10 : 10 ≤ t)
    (htk : t ≤ k) (u : Fin k → Fin n → F) (j : Fin k) :
    ((Finset.univ.filter (fun v : Fin n → F => GG f Γ t (Function.update u j v) j)).card : ℝ) ≤
      (((Fintype.card F : ℝ) ^ 3 * (k : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ t) *
        (Fintype.card (Fin n → F) : ℝ)) := by
  have hiff : ∀ v, GG f Γ t (Function.update u j v) j ↔
      ((tPre f Γ u j ∧ badPre f Γ t u j) ∧
        rho (Fintype.card F) k * dv u f j <
          |relDev (consSeq u j ⊔ Submodule.span F {v}) f|) := by
    intro v
    have h1 := consSeq_update_lt u j v j le_rfl
    have h2 := consSeq_update_succ u j v
    unfold GG tPre badStep badPre dv
    rw [h1, h2]
    tauto
  by_cases hpre : tPre f Γ u j ∧ badPre f Γ t u j
  · have := bound_pre hf Γ hΓ t ht10 htk u j hpre.1 hpre.2
    refine le_trans (le_of_eq ?_) this
    congr 2
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hiff]
    simp [hpre]
  · have : (Finset.univ.filter (fun v : Fin n → F => GG f Γ t (Function.update u j v) j)) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rw [hiff]
      tauto
    rw [this]
    have hk10 : (10 : ℝ) ≤ k := ht10.trans htk
    have hq0 : 0 < (Fintype.card F : ℝ) := by have := two_le_card (F := F); linarith
    have : 0 < Fintype.card (Fin n → F) := Fintype.card_pos
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

lemma final_arith (q : ℝ) (hq : 2 ≤ q) (t : ℝ) (k : ℕ) (hk : (k : ℝ) ≤ q ^ (t / 20))
    (ht10 : 10 ≤ t) (hk1 : 1 ≤ (k : ℝ)) :
    ((k : ℝ) * (q ^ 3 * (k : ℝ) ^ 2 / q ^ t)) ^ (⌈t / 4⌉₊) ≤ q ^ (-(1 / 10 : ℝ) * t ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hqt : 0 < q ^ t := Real.rpow_pos_of_pos hq0 t
  have hbase : (k : ℝ) * (q ^ 3 * (k : ℝ) ^ 2 / q ^ t) ≤ q ^ (3 - 17 * t / 20) := by
    have h1 : (k : ℝ) ^ 3 ≤ (q ^ (t / 20)) ^ 3 := pow_le_pow_left₀ hk0 hk 3
    have h2 : (q ^ (t / 20)) ^ 3 = q ^ (3 * t / 20) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
    have h3 : q ^ (3 - 17 * t / 20) = q ^ 3 * q ^ (3 * t / 20) / q ^ t := by
      have : (3 - 17 * t / 20 : ℝ) = 3 + 3 * t / 20 - t := by ring
      rw [this, Real.rpow_sub hq0, Real.rpow_add hq0]
      norm_cast
    rw [h3]
    have : (k : ℝ) * (q ^ 3 * (k : ℝ) ^ 2 / q ^ t) = q ^ 3 * (k : ℝ) ^ 3 / q ^ t := by ring
    rw [this]
    apply div_le_div_of_nonneg_right _ hqt.le
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hnn : 0 ≤ (k : ℝ) * (q ^ 3 * (k : ℝ) ^ 2 / q ^ t) := by positivity
  calc ((k : ℝ) * (q ^ 3 * (k : ℝ) ^ 2 / q ^ t)) ^ (⌈t / 4⌉₊)
      ≤ (q ^ (3 - 17 * t / 20)) ^ (⌈t / 4⌉₊) := pow_le_pow_left₀ hnn hbase _
    _ = q ^ ((3 - 17 * t / 20) * (⌈t / 4⌉₊ : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    _ ≤ q ^ (-(1 / 10 : ℝ) * t ^ 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hq1
        have hτ : t / 4 ≤ (⌈t / 4⌉₊ : ℝ) := Nat.le_ceil _
        have hneg : 3 - 17 * t / 20 ≤ 0 := by linarith
        nlinarith

end RLCDiscrepancy.Dev.L413b

namespace RLCDiscrepancy
open RLCDiscrepancy.Dev.L413b in
theorem chk_lemma_4_13_of_ten_le {F : Type*} [Field F] [Fintype F] (n k : ℕ) (hkn : k ≤ n)
    (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (Γ : ℝ) (hΓ : 0 < Γ) (t : ℝ)
    (ht : 20 * Real.logb (Fintype.card F) n ≤ t) (htk : t ≤ k) (ht10 : 10 ≤ t) :
    PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧
          IsMonotone u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) ∧
          ¬ IsSmooth u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) ≤
      (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) := by
  have hq2 : (2 : ℝ) ≤ (Fintype.card F : ℝ) := two_le_card
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hk10 : (10 : ℝ) ≤ k := ht10.trans htk
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hkq : (k : ℝ) ≤ (Fintype.card F : ℝ) ^ (t / 20) := by
    have hn0 : (0 : ℝ) < n := by
      have : (k : ℝ) ≤ n := by exact_mod_cast hkn
      linarith
    have h1 : Real.logb (Fintype.card F) n ≤ t / 20 := by linarith
    have h2 := (Real.logb_le_iff_le_rpow (by linarith) hn0).1 h1
    exact le_trans (by exact_mod_cast hkn) h2
  have hN : (0 : ℝ) < (Fintype.card (Fin n → F) : ℝ) := by
    have : 0 < Fintype.card (Fin n → F) := Fintype.card_pos
    exact_mod_cast this
  have hp0 : 0 ≤ (Fintype.card F : ℝ) ^ 3 * (k : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ t := by positivity
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (Fintype.card F : ℝ) ^ 3 * (k : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ t :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ, τ = ⌈t / 4⌉₊ := ⟨_, rfl⟩
  rw [← hp] at hp0
  have hstep : ∀ (j : Fin k) (u : Fin k → Fin n → F),
      ((Finset.univ.filter (fun v : Fin n → F => GG f Γ t (Function.update u j v) j)).card : ℝ) ≤
        p * (Fintype.card (Fin n → F) : ℝ) := by
    intro j u; rw [hp]; exact step_bound hf Γ hΓ t ht10 htk u j
  have hdep : ∀ (j : Fin k) (u u' : Fin k → Fin n → F), (∀ i, i ≤ j → u i = u' i) →
      (GG f Γ t u j ↔ GG f Γ t u' j) := fun j u u' h => GG_dep f Γ t j u u' h
  have hprod : ∀ S : Finset (Fin k),
      ((Finset.univ.filter (fun u : Fin k → Fin n → F => ∀ j ∈ S, GG f Γ t u j)).card : ℝ) ≤
        p ^ S.card * (Fintype.card (Fin n → F) : ℝ) ^ k :=
    RLCDiscrepancy.Dev.L413bProd.card_forall_le (V := Fin n → F) (k := k)
      (fun j u => GG f Γ t u j) p hp0 hdep hstep
  have hsub : (Finset.univ.filter (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧
          IsMonotone u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) ∧
          ¬ IsSmooth u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k)) ⊆
      (Finset.powersetCard τ (Finset.univ : Finset (Fin k))).biUnion
        (fun S => Finset.univ.filter (fun u : Fin k → Fin n → F => ∀ j ∈ S, GG f Γ t u j)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨hF, hmono, hns⟩ := hu
    obtain ⟨B, hB, hcard⟩ := exists_bad hf Γ hΓ t ht10 htk u hmono hns
    have hτB : τ ≤ B.card := by rw [hτ]; exact Nat.ceil_le.2 hcard
    obtain ⟨S0, hS0, hS0c⟩ := Finset.exists_subset_card_eq hτB
    have hlt : ∀ m ∈ S0, m < k := fun m hm => (hB m (hS0 hm)).1
    rw [Finset.mem_biUnion]
    refine ⟨S0.attachFin hlt, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, by rw [Finset.card_attachFin, hS0c]⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj
      rw [Finset.mem_attachFin] at hj
      exact ⟨hF j j.2.le, (hB j (hS0 hj)).2⟩
  have hcardE : ((Finset.univ.filter (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧
          IsMonotone u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) ∧
          ¬ IsSmooth u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k)).card : ℝ) ≤
      (k : ℝ) ^ τ * (p ^ τ * (Fintype.card (Fin n → F) : ℝ) ^ k) := by
    calc _ ≤ ((((Finset.powersetCard τ (Finset.univ : Finset (Fin k))).biUnion
        (fun S => Finset.univ.filter (fun u : Fin k → Fin n → F => ∀ j ∈ S, GG f Γ t u j))).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((∑ S ∈ Finset.powersetCard τ (Finset.univ : Finset (Fin k)),
          (Finset.univ.filter (fun u : Fin k → Fin n → F => ∀ j ∈ S, GG f Γ t u j)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ S ∈ Finset.powersetCard τ (Finset.univ : Finset (Fin k)),
          ((Finset.univ.filter (fun u : Fin k → Fin n → F => ∀ j ∈ S, GG f Γ t u j)).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ S ∈ Finset.powersetCard τ (Finset.univ : Finset (Fin k)),
          (p ^ τ * (Fintype.card (Fin n → F) : ℝ) ^ k) := by
          apply Finset.sum_le_sum
          intro S hS
          rw [Finset.mem_powersetCard] at hS
          have := hprod S
          rwa [hS.2] at this
      _ = (k.choose τ : ℝ) * (p ^ τ * (Fintype.card (Fin n → F) : ℝ) ^ k) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ ≤ (k : ℝ) ^ τ * (p ^ τ * (Fintype.card (Fin n → F) : ℝ) ^ k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Nat.choose_le_pow k τ
  unfold PunctSketch.coinProb
  have hΩ : (Fintype.card (Fin k → Fin n → F) : ℝ) = (Fintype.card (Fin n → F) : ℝ) ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin]; push_cast; rfl
  rw [hΩ, div_le_iff₀ (by positivity)]
  refine le_trans (le_of_eq ?_) (hcardE.trans ?_)
  · congr 1
    apply congrArg
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hfa := final_arith (Fintype.card F : ℝ) hq2 t k hkq ht10 hk1
  rw [← hτ, ← hp] at hfa
  calc (k : ℝ) ^ τ * (p ^ τ * (Fintype.card (Fin n → F) : ℝ) ^ k)
      = ((k : ℝ) * p) ^ τ * (Fintype.card (Fin n → F) : ℝ) ^ k := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hfa


end RLCDiscrepancy
end

theorem solution : type_of% @RLCDiscrepancy.chk_lemma_4_13_of_ten_le := @RLCDiscrepancy.chk_lemma_4_13_of_ten_le

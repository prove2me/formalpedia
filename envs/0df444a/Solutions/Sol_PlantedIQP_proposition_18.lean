-- Prove2me | solution 1 for PlantedIQP.proposition_18
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:49:52.645837+00:00
-- url     : https://prove2.me/submissions/fa37e76b-3e70-4d4f-9e38-0179e12f4f64

import Mathlib
import Definitions.Def_PlantedIQP_comp
import Definitions.Def_PlantedIQP_triForm
import Definitions.Def_PlantedIQP_hessSlice
import Theorems.Thm_PlantedIQP_lemma_16
import Theorems.Thm_PlantedIQP_theorem_17

set_option autoImplicit false

namespace AuxProp18

open PlantedIQP

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  rcases zmod2_eq_zero_or_one x with h | h <;> simp [h]

lemma vec_eq_indicator {ι : Type*} [DecidableEq ι] [Fintype ι] (x : ι → ZMod 2) :
    x = indicatorVec (Finset.univ.filter fun i => x i = 1) := by
  ext i
  simp only [indicatorVec, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases zmod2_eq_zero_or_one (x i) with h | h <;> simp [h]

lemma prod_indicatorVec {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (∏ i ∈ S, indicatorVec T i) = if S ⊆ T then 1 else 0 := by
  by_cases h : S ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [indicatorVec, h hi]
  · rw [if_neg h]
    rw [Finset.not_subset] at h
    rcases h with ⟨i, hiS, hiT⟩
    exact Finset.prod_eq_zero hiS (by simp [indicatorVec, hiT])

lemma sum_mobiusCoeff_powerset {ι : Type*} [DecidableEq ι]
    (F : (ι → ZMod 2) → ZMod 2) (U : Finset ι) :
    (∑ S ∈ U.powerset, mobiusCoeff F S) = F (indicatorVec U) := by
  classical
  simp only [mobiusCoeff]
  have hswap :
      (∑ S ∈ U.powerset, ∑ T ∈ S.powerset, F (indicatorVec T)) =
        ∑ T ∈ U.powerset, ∑ S ∈ U.powerset.filter (fun S => T ⊆ S), F (indicatorVec T) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_filter] at hp ⊢
      exact ⟨hp.2.trans hp.1, hp.1, hp.2⟩
    · rintro ⟨S₁, T₁⟩ _ ⟨S₂, T₂⟩ _ h
      cases h
      rfl
    · rintro ⟨T, S⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_filter] at hp
      exact ⟨⟨S, T⟩, by simp [hp.2.1, hp.2.2], rfl⟩
    · rintro ⟨S, T⟩ _
      rfl
  rw [hswap]
  have hcard : ∀ T ∈ U.powerset,
      (U.powerset.filter (fun S => T ⊆ S)).card = 2 ^ (U \ T).card := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hbij : (U.powerset.filter (fun S => T ⊆ S)).card = (U \ T).powerset.card := by
      refine Finset.card_bij (fun S _ => S \ T) ?_ ?_ ?_
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
        exact Finset.sdiff_subset_sdiff hS.1 subset_rfl
      · intro S₁ hS₁ S₂ hS₂ hEq
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS₁ hS₂
        have h1 : S₁ = (S₁ \ T) ∪ T := (Finset.sdiff_union_of_subset hS₁.2).symm
        have h2 : S₂ = (S₂ \ T) ∪ T := (Finset.sdiff_union_of_subset hS₂.2).symm
        rw [h1, h2, hEq]
      · intro W hW
        rw [Finset.mem_powerset] at hW
        refine ⟨W ∪ T, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.union_subset (hW.trans Finset.sdiff_subset) hT, Finset.subset_union_right⟩
        · apply Finset.ext
          intro x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hx | hx, hnx⟩
            · exact hx
            · exact absurd hx hnx
          · intro hx
            exact ⟨Or.inl hx, (Finset.mem_sdiff.mp (hW hx)).2⟩
    rw [hbij, Finset.card_powerset]
  have hterm : ∀ T ∈ U.powerset,
      (∑ _S ∈ U.powerset.filter (fun S => T ⊆ S), F (indicatorVec T)) =
        if T = U then F (indicatorVec U) else 0 := by
    intro T hT
    rw [Finset.sum_const, hcard T hT, nsmul_eq_mul]
    rw [Finset.mem_powerset] at hT
    by_cases hTU : T = U
    · subst hTU
      simp
    · rw [if_neg hTU]
      have hne : (U \ T).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
        intro hempty
        apply hTU
        exact Finset.Subset.antisymm hT (Finset.sdiff_eq_empty_iff_subset.mp hempty))
      rcases Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hne) with ⟨m, hm⟩
      rw [hm]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      simp [pow_succ, h2]
  rw [Finset.sum_congr rfl hterm]
  simp

lemma mobius_eval {ι : Type*} [DecidableEq ι] [Fintype ι]
    (F : (ι → ZMod 2) → ZMod 2) (x : ι → ZMod 2) :
    (∑ S : Finset ι, mobiusCoeff F S * ∏ i ∈ S, x i) = F x := by
  classical
  let U := Finset.univ.filter fun i => x i = 1
  have hx : x = indicatorVec U := vec_eq_indicator x
  conv_rhs => rw [hx]
  conv_lhs =>
    arg 2; ext S; rw [hx, prod_indicatorVec]
  have hsub : ∀ S : Finset ι,
      (mobiusCoeff F S * if S ⊆ U then (1 : ZMod 2) else 0) =
        if S ∈ U.powerset then mobiusCoeff F S else 0 := by
    intro S
    by_cases h : S ⊆ U <;> simp [Finset.mem_powerset, h]
  simp_rw [hsub]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact sum_mobiusCoeff_powerset F U

lemma mobiusCoeff_add {ι : Type*} [DecidableEq ι]
    (F G : (ι → ZMod 2) → ZMod 2) (S : Finset ι) :
    mobiusCoeff (fun x => F x + G x) S = mobiusCoeff F S + mobiusCoeff G S := by
  simp [mobiusCoeff, Finset.sum_add_distrib]

lemma mobiusCoeff_sum {ι α : Type*} [DecidableEq ι] (s : Finset α)
    (F : α → (ι → ZMod 2) → ZMod 2) (S : Finset ι) :
    mobiusCoeff (fun x => ∑ a ∈ s, F a x) S = ∑ a ∈ s, mobiusCoeff (F a) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mobiusCoeff]
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [mobiusCoeff_add, ih]

lemma mobiusCoeff_const_mul {ι : Type*} [DecidableEq ι]
    (c : ZMod 2) (F : (ι → ZMod 2) → ZMod 2) (S : Finset ι) :
    mobiusCoeff (fun x => c * F x) S = c * mobiusCoeff F S := by
  simp [mobiusCoeff, Finset.mul_sum]

lemma mobiusCoeff_monomial_eq_zero_of_lt {ι : Type*} [DecidableEq ι]
    (U S : Finset ι) (h : U.card < S.card) :
    mobiusCoeff (fun x => ∏ i ∈ U, x i) S = 0 := by
  classical
  simp only [mobiusCoeff, prod_indicatorVec]
  by_cases hUS : U ⊆ S
  · rw [Finset.sum_boole]
    have hcard : (S.powerset.filter (fun T => U ⊆ T)).card = 2 ^ (S \ U).card := by
      have hbij : (S.powerset.filter (fun T => U ⊆ T)).card = (S \ U).powerset.card := by
        refine Finset.card_bij (fun T _ => T \ U) ?_ ?_ ?_
        · intro T hT
          simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
          exact Finset.sdiff_subset_sdiff hT.1 subset_rfl
        · intro T₁ hT₁ T₂ hT₂ hEq
          simp only [Finset.mem_filter, Finset.mem_powerset] at hT₁ hT₂
          rw [← Finset.sdiff_union_of_subset hT₁.2, ← Finset.sdiff_union_of_subset hT₂.2, hEq]
        · intro W hW
          rw [Finset.mem_powerset] at hW
          refine ⟨W ∪ U, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finset.union_subset (hW.trans Finset.sdiff_subset) hUS, Finset.subset_union_right⟩
          · apply Finset.ext
            intro x
            simp only [Finset.mem_sdiff, Finset.mem_union]
            constructor
            · rintro ⟨hx | hx, hnx⟩
              · exact hx
              · exact absurd hx hnx
            · intro hx
              exact ⟨Or.inl hx, (Finset.mem_sdiff.mp (hW hx)).2⟩
      rw [hbij, Finset.card_powerset]
    rw [hcard]
    have hpos : 0 < (S \ U).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUS]
      omega
    rcases Nat.exists_eq_succ_of_ne_zero hpos.ne' with ⟨m, hm⟩
    rw [hm]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [pow_succ, h2]
  · apply Finset.sum_eq_zero
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [if_neg (fun hUT => hUS (hUT.trans hT))]

lemma prod_vars_eq_prod_image {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset α) (g : α → ι) (x : ι → ZMod 2) :
    (∏ a ∈ s, x (g a)) = ∏ i ∈ s.image g, x i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.image_insert]
    by_cases hmem : g a ∈ s.image g
    · rw [Finset.insert_eq_of_mem hmem]
      rw [← Finset.mul_prod_erase (s.image g) (fun i => x i) hmem, ← mul_assoc, zmod2_mul_self]
    · rw [Finset.prod_insert hmem]

lemma degLE_prod_linear_finset {ι α : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq α]
    (s : Finset α) (L : α → ι → ZMod 2) {d : ℕ} (hs : s.card ≤ d) :
    DegLE (fun x : ι → ZMod 2 => ∏ a ∈ s, ∑ i : ι, L a i * x i) d := by
  intro S hS
  have hexp : ∀ x : ι → ZMod 2,
      (∏ a ∈ s, ∑ i : ι, L a i * x i) =
        ∑ g ∈ s.pi (fun _ : α => (Finset.univ : Finset ι)),
          (∏ a ∈ s.attach, L a.1 (g a.1 a.2)) * (∏ a ∈ s.attach, x (g a.1 a.2)) := by
    intro x
    rw [Finset.prod_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.prod_mul_distrib]
  simp_rw [hexp]
  rw [mobiusCoeff_sum]
  apply Finset.sum_eq_zero
  intro g _
  rw [mobiusCoeff_const_mul]
  have himg : ∀ x : ι → ZMod 2,
      (∏ a ∈ s.attach, x (g a.1 a.2)) =
        ∏ i ∈ s.attach.image (fun a => g a.1 a.2), x i :=
    prod_vars_eq_prod_image s.attach (fun a => g a.1 a.2)
  simp_rw [himg]
  have hlt : (s.attach.image (fun a => g a.1 a.2)).card < S.card := by
    calc (s.attach.image (fun a => g a.1 a.2)).card
      _ ≤ s.attach.card := Finset.card_image_le
      _ = s.card := Finset.card_attach
      _ ≤ d := hs
      _ < S.card := hS
  rw [mobiusCoeff_monomial_eq_zero_of_lt _ _ hlt, mul_zero]

lemma degLE_eval_linear {n : ℕ} {ι : Type*} [DecidableEq ι] [Fintype ι]
    (f : CubicPoly n) (M : (ι → ZMod 2) →ₗ[ZMod 2] Vec n) :
    DegLE (fun y : ι → ZMod 2 => f.eval (M y)) 3 := by
  intro S hS
  have hM : ∀ (y : ι → ZMod 2) (i : Fin n),
      M y i = ∑ j : ι, M (Pi.single j 1) i * y j := by
    intro y i
    have hy : y = ∑ j : ι, y j • Pi.single j (1 : ZMod 2) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  simp only [CubicPoly.eval]
  rw [mobiusCoeff_add, mobiusCoeff_add, mobiusCoeff_sum, mobiusCoeff_sum, mobiusCoeff_sum]
  have h3 : ∑ m : Mono n 3, mobiusCoeff (fun y => f.c3 m * ∏ i ∈ m.1, M y i) S = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    rw [mobiusCoeff_const_mul]
    have hfn : (fun y : ι → ZMod 2 => ∏ i ∈ m.1, M y i) =
        fun y => ∏ i ∈ m.1, ∑ j : ι, M (Pi.single j 1) i * y j := by
      ext y; exact Finset.prod_congr rfl fun i _ => hM y i
    rw [hfn]
    have hd := degLE_prod_linear_finset m.1 (fun i j => M (Pi.single j 1) i) (le_of_eq m.2) S hS
    rw [hd, mul_zero]
  have h2 : ∑ m : Mono n 2, mobiusCoeff (fun y => f.c2 m * ∏ i ∈ m.1, M y i) S = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    rw [mobiusCoeff_const_mul]
    have hfn : (fun y : ι → ZMod 2 => ∏ i ∈ m.1, M y i) =
        fun y => ∏ i ∈ m.1, ∑ j : ι, M (Pi.single j 1) i * y j := by
      ext y; exact Finset.prod_congr rfl fun i _ => hM y i
    rw [hfn]
    have hd := degLE_prod_linear_finset m.1 (fun i j => M (Pi.single j 1) i)
      (by omega : m.1.card ≤ 3) S hS
    rw [hd, mul_zero]
  have h1 : ∑ i : Fin n, mobiusCoeff (fun y => f.c1 i * M y i) S = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [mobiusCoeff_const_mul]
    have hfn : (fun y : ι → ZMod 2 => M y i) =
        fun y => ∏ a ∈ ({i} : Finset (Fin n)), ∑ j : ι, M (Pi.single j 1) a * y j := by
      ext y; simp [hM y i]
    rw [hfn]
    have hd := degLE_prod_linear_finset ({i} : Finset (Fin n))
      (fun a j => M (Pi.single j 1) a) (by simp) S hS
    rw [hd, mul_zero]
  rw [h3, h2, h1, add_zero, add_zero]

lemma ofFun_eval {n : ℕ} (F : Vec n → ZMod 2) (h0 : F 0 = 0) (hdeg : DegLE F 3) (x : Vec n) :
    (CubicPoly.ofFun F).eval x = F x := by
  classical
  rw [← mobius_eval F x]
  simp only [CubicPoly.eval, CubicPoly.ofFun]
  have hcard : ∀ S : Finset (Fin n),
      mobiusCoeff F S * (∏ i ∈ S, x i) =
        if S.card = 3 then mobiusCoeff F S * (∏ i ∈ S, x i)
        else if S.card = 2 then mobiusCoeff F S * (∏ i ∈ S, x i)
        else if S.card = 1 then mobiusCoeff F S * (∏ i ∈ S, x i)
        else 0 := by
    intro S
    by_cases hc3 : S.card = 3
    · simp [hc3]
    · by_cases hc2 : S.card = 2
      · simp [hc2]
      · by_cases hc1 : S.card = 1
        · simp [hc1]
        · simp only [hc3, hc2, hc1, ↓reduceIte]
          by_cases hc0 : S.card = 0
          · rw [Finset.card_eq_zero] at hc0
            subst hc0
            have hm0 : mobiusCoeff F ∅ = 0 := by
              have hi0 : indicatorVec (∅ : Finset (Fin n)) = 0 := by
                ext i; simp [indicatorVec]
              simp [mobiusCoeff, hi0, h0]
            simp [hm0]
          · have hgt : 3 < S.card := by omega
            rw [hdeg S hgt, zero_mul]
  conv_rhs =>
    arg 2; ext S; rw [hcard S]
  have hsplit :
      (∑ S : Finset (Fin n),
        if S.card = 3 then mobiusCoeff F S * (∏ i ∈ S, x i)
        else if S.card = 2 then mobiusCoeff F S * (∏ i ∈ S, x i)
        else if S.card = 1 then mobiusCoeff F S * (∏ i ∈ S, x i)
        else 0) =
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = 3), mobiusCoeff F S * ∏ i ∈ S, x i) +
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = 2), mobiusCoeff F S * ∏ i ∈ S, x i) +
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = 1), mobiusCoeff F S * ∏ i ∈ S, x i) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases h3 : S.card = 3 <;> by_cases h2 : S.card = 2 <;> by_cases h1 : S.card = 1 <;>
      (try omega) <;> simp [h3, h2, h1]
  rw [hsplit]
  have hsub3 :
      (∑ S : Mono n 3, mobiusCoeff F S.1 * ∏ i ∈ S.1, x i) =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = 3),
          mobiusCoeff F S * ∏ i ∈ S, x i := by
    refine (Finset.sum_subtype (Finset.univ.filter fun S : Finset (Fin n) => S.card = 3)
      (fun S => by simp) (fun S => mobiusCoeff F S * ∏ i ∈ S, x i)).symm
  have hsub2 :
      (∑ S : Mono n 2, mobiusCoeff F S.1 * ∏ i ∈ S.1, x i) =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = 2),
          mobiusCoeff F S * ∏ i ∈ S, x i := by
    refine (Finset.sum_subtype (Finset.univ.filter fun S : Finset (Fin n) => S.card = 2)
      (fun S => by simp) (fun S => mobiusCoeff F S * ∏ i ∈ S, x i)).symm
  have hsub1 :
      (∑ i : Fin n, mobiusCoeff F {i} * x i) =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = 1),
          mobiusCoeff F S * ∏ i ∈ S, x i := by
    refine Finset.sum_bij (fun i _ => ({i} : Finset (Fin n))) ?_ ?_ ?_ ?_
    · intro i _; simp
    · intro i _ j _ h; exact Finset.singleton_injective h
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_one] at hS
      rcases hS with ⟨i, rfl⟩
      exact ⟨i, Finset.mem_univ i, rfl⟩
    · intro i _; simp
  rw [hsub3, hsub2, hsub1]

lemma eval_zero {n : ℕ} (f : CubicPoly n) : f.eval 0 = 0 := by
  simp only [CubicPoly.eval, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have h3 : ∀ S : Mono n 3, (∏ i ∈ S.1, (0 : ZMod 2)) = 0 := by
    intro S
    rcases Finset.card_pos.mp (by rw [S.2]; omega) with ⟨i, hi⟩
    exact Finset.prod_eq_zero hi rfl
  have h2 : ∀ S : Mono n 2, (∏ i ∈ S.1, (0 : ZMod 2)) = 0 := by
    intro S
    rcases Finset.card_pos.mp (by rw [S.2]; omega) with ⟨i, hi⟩
    exact Finset.prod_eq_zero hi rfl
  simp [h3, h2]

lemma comp_eval {n : ℕ} (f : CubicPoly n) (A : Matrix.GeneralLinearGroup (Fin n) (ZMod 2))
    (x : Vec n) :
    (f.comp A).eval x = f.eval (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) x) := by
  apply ofFun_eval
  · simp [eval_zero]
  · exact degLE_eval_linear f (Matrix.mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2)))

lemma triForm_comp {n : ℕ} (f : CubicPoly n) (A : Matrix.GeneralLinearGroup (Fin n) (ZMod 2))
    (u v w : Vec n) :
    triForm (f.comp A) u v w =
      triForm f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u)
        (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) v)
        (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) w) := by
  rw [lemma_16, lemma_16]
  simp only [comp_eval, Matrix.mulVec_add]

lemma triForm_stdBasis {n : ℕ} (g : CubicPoly n) (i j k : Fin n) :
    triForm g (stdBasis i) (stdBasis j) (stdBasis k) = g.coeff3 i j k := by
  simp only [triForm, stdBasis]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro c _ hck; simp [Pi.single_eq_of_ne hck]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    · intro b _ hbj
      apply Finset.sum_eq_zero; intro c _; simp [Pi.single_eq_of_ne hbj]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · intro a _ hai
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _; simp [Pi.single_eq_of_ne hai]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma c3_eq_of_triForm_eq {n : ℕ} (g₁ g₂ : CubicPoly n)
    (h : ∀ u v w : Vec n, triForm g₁ u v w = triForm g₂ u v w) :
    g₁.c3 = g₂.c3 := by
  ext S
  rcases Finset.card_eq_three.mp S.2 with ⟨i, j, k, _, _, _, hS⟩
  have hcard : ({i, j, k} : Finset (Fin n)).card = 3 := by rw [← hS]; exact S.2
  have h1 : g₁.coeff3 i j k = g₁.c3 S := by
    simp only [CubicPoly.coeff3, dif_pos hcard]
    congr 1; ext1; exact hS.symm
  have h2 : g₂.coeff3 i j k = g₂.c3 S := by
    simp only [CubicPoly.coeff3, dif_pos hcard]
    congr 1; ext1; exact hS.symm
  rw [← h1, ← h2, ← triForm_stdBasis, ← triForm_stdBasis, h]

end AuxProp18

open PlantedIQP AuxProp18

theorem solution {n : ℕ} (f : CubicPoly n) (A : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    (f.comp A).cubicPart = (f.cubicPart.comp A).cubicPart ∧
      (∀ u v w : Vec n, triForm (f.comp A) u v w =
        triForm f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u)
          (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) v)
          (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) w)) ∧
      ∀ u : Vec n,
        sliceMatrix (f.comp A) u = Matrix.transpose (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
            sliceMatrix f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u) *
              (A : Matrix (Fin n) (Fin n) (ZMod 2)) ∧
          hessSlice (f.comp A) u + quadMatrix (f.comp A) =
            Matrix.transpose (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (hessSlice f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u) + quadMatrix f) *
                (A : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  refine ⟨?_, triForm_comp f A, ?_⟩
  · ext S <;> simp only [CubicPoly.cubicPart]
    · refine congr_fun (c3_eq_of_triForm_eq (f.comp A) (f.cubicPart.comp A) fun u v w => ?_) S
      rw [triForm_comp, triForm_comp]
      rfl
  · intro u
    have hslice : sliceMatrix (f.comp A) u =
        Matrix.transpose (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
          sliceMatrix f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u) *
            (A : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      ext i j
      simp only [sliceMatrix, Matrix.of_apply]
      rw [triForm_comp]
      have h17 := theorem_17 f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u)
      rw [h17.2, ← h17.1]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, stdBasis]
      have hcol : ∀ (a : Fin n) (r : Fin n),
          (∑ k : Fin n, (A : Matrix (Fin n) (Fin n) (ZMod 2)) a k *
            (Pi.single r (1 : ZMod 2) : Vec n) k) =
            (A : Matrix (Fin n) (Fin n) (ZMod 2)) a r := by
        intro a r
        rw [Finset.sum_eq_single r]
        · simp
        · intro k _ hkr; simp [Pi.single_eq_of_ne hkr]
        · intro hr; exact absurd (Finset.mem_univ r) hr
      simp_rw [hcol, Finset.sum_mul]
      rw [Finset.sum_comm]
      rfl
    refine ⟨hslice, ?_⟩
    rw [← (theorem_17 (f.comp A) u).1,
      ← (theorem_17 f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u)).1]
    exact hslice

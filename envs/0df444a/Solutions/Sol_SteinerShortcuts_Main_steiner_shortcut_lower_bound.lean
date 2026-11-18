-- Prove2me | solution 1 for SteinerShortcuts.Main.steiner_shortcut_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:18:22.201207+00:00
-- url     : https://prove2.me/submissions/104f3a16-e23b-4113-8b48-efd9b42a648c

import Theorems.Thm_SteinerShortcuts_Main_equation_11
import Theorems.Thm_SteinerShortcuts_Main_construction_shortcut_tradeoff
import Mathlib
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

private noncomputable def rateExponent (ε : ℝ) : ℝ := (1-57*ε)/56
private noncomputable def lowerConstant (c C ε A : ℝ) : ℝ :=
  min 1 (c/(4*(A+C)*(C^ε)*(C^(rateExponent ε))))

private theorem lower_constant_pos (c C ε A : ℝ) (hc : 0 < c) (hC : 0 < C) (hA : 0 < A) :
    0  <  lowerConstant c C ε A := by
  unfold lowerConstant
  apply lt_min zero_lt_one
  apply div_pos hc
  exact mul_pos (mul_pos (mul_pos (by norm_num) (add_pos hA hC))
    (Real.rpow_pos_of_pos hC ε)) (Real.rpow_pos_of_pos hC _)

private theorem diameter_power_bound (c C ε A L n m p e D : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hA : 0 < A) (hL : 4 ≤ L)
    (hn : 1 ≤ n) (hm : (1 : ℝ)  ≤  m) (he : 0 ≤ e) (hD : 1 ≤ D)
    (hpL : c*m ≤ p) (hpU : p ≤ C*m) (hnU : n ≤ C*L^56) (hmU : m ≤ C*L^57)
    (hcount : p*(L-1) ≤ (e+p)*(D+1)) (hbudget : e ≤ A*(m^(1+ε))) :
    lowerConstant c C ε A*(n^(rateExponent ε))  ≤  D := by
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hmp : 0 < m := by linarith
  have hp0 : 0 ≤ p := by have hh:=mul_pos hc hmp;linarith
  have hbpos := lower_constant_pos c C ε A hc hC hA
  by_cases hex : rateExponent ε  ≤  0
  · have hnpow := Real.rpow_le_one_of_one_le_of_nonpos hn hex
    have hb1 : lowerConstant c C ε A ≤ 1 := min_le_left _ _
    have hh := mul_le_mul_of_nonneg_left hnpow hbpos.le
    have hh2 : lowerConstant c C ε A * (n^(rateExponent ε)) ≤ lowerConstant c C ε A := by simpa only [mul_one] using hh
    exact hh2.trans (hb1.trans hD)
  · have hexp : 0 < rateExponent ε := by linarith
    have hpow : (m^(1+ε))=m*(m^ε) := by
      rw [Real.rpow_add hmp,Real.rpow_one]
    have hmle : m ≤ (m^(1+ε)) := by
      rw [hpow]
      have hh := Real.one_le_rpow hm hε.le
      nlinarith
    have hep : e+p ≤ (A+C)*(m^(1+ε)) := by
      have hh := mul_le_mul_of_nonneg_left hmle hC.le
      nlinarith
    have hleft : (c*m)*(L/2) ≤ p*(L-1) :=
      mul_le_mul hpL (by linarith) (by linarith) hp0
    have hright : (e+p)*(D+1) ≤ ((A+C)*(m^(1+ε)))*(2*D) :=
      mul_le_mul hep (by linarith) (by linarith) (mul_nonneg (add_pos hA hC).le (Real.rpow_nonneg hm0 _))
    have hcombined := hleft.trans (hcount.trans hright)
    rw [hpow] at hcombined
    have hcancel : c*L ≤ 4*(A+C)*(m^ε)*D := by
      apply (mul_le_mul_iff_left₀ hmp).mp
      nlinarith [hcombined]
    have hLm : ((L^57)^ε)=(L^(57*ε)) := by
      rw [← Real.rpow_natCast L 57,← Real.rpow_mul hL0]
      norm_num
    have hmr := Real.rpow_le_rpow hm0 hmU hε.le
    rw [Real.mul_rpow hC.le (pow_nonneg hL0 57),hLm] at hmr
    let K : ℝ := 4*(A+C)*(C^ε)
    have hK : 0 < K := by dsimp [K];positivity
    have hbound : c*L ≤ K*(L^(57*ε))*D := by
      calc c*L  ≤  4*(A+C)*(m^ε)*D := hcancel
           _  ≤  4*(A+C)*((C^ε)*(L^(57*ε)))*D := by gcongr
           _ = K*(L^(57*ε))*D := by dsimp [K];ring
    have hfactor : (L^(57*ε))*(L^(1-57*ε))=L := by
      rw [← Real.rpow_add hLp]
      norm_num
    have hbase : c*(L^(1-57*ε)) ≤ K*D := by
      apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hLp (57*ε))).mp
      calc (L^(57*ε))*(c*(L^(1-57*ε))) = c*L := by
             calc _ = c*((L^(57*ε))*(L^(1-57*ε))) := by ring
                  _ = c*L := by rw [hfactor]
           _  ≤  K*(L^(57*ε))*D := hbound
           _ = (L^(57*ε))*(K*D) := by ring
    have hLn : ((L^56)^(rateExponent ε))=(L^(1-57*ε)) := by
      rw [← Real.rpow_natCast L 56,← Real.rpow_mul hL0]
      congr 1
      unfold rateExponent
      ring
    have hnr := Real.rpow_le_rpow hn0 hnU hexp.le
    rw [Real.mul_rpow hC.le (pow_nonneg hL0 56),hLn] at hnr
    have hb : lowerConstant c C ε A ≤ c/(K*(C^(rateExponent ε))) := by
      simpa only [lowerConstant,K,mul_assoc] using min_le_right (1:ℝ)
        (c/(4*(A+C)*(C^ε)*(C^(rateExponent ε))))
    have hCP : 0 < (C^(rateExponent ε)) := Real.rpow_pos_of_pos hC _
    have hKn : K≠0 := ne_of_gt hK
    have hCn : (C^(rateExponent ε))≠0 := ne_of_gt hCP
    calc lowerConstant c C ε A*(n^(rateExponent ε))
           ≤  (c/(K*(C^(rateExponent ε))))*(n^(rateExponent ε)) :=
            mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hn0 _)
         _  ≤  (c/(K*(C^(rateExponent ε))))*((C^(rateExponent ε))*(L^(1-57*ε))) :=
            mul_le_mul_of_nonneg_left hnr (by positivity)
         _ = (c*(L^(1-57*ε)))/K := by field_simp
         _  ≤  D := (div_le_iff₀ hK).mpr (by nlinarith [hbase])

open SteinerShortcuts.Main
set_option maxHeartbeats 1000000

private theorem family_admissible (k : ℕ) : Admissible (familyLayers k) (familyPrime k) := by
  have hL : 4 ≤ familyLayers k := by unfold familyLayers;omega
  have h0 : familyLayers k ≠ 0 := by omega
  have hp := Nat.find_spec (Nat.exists_prime_lt_and_le_two_mul (familyLayers k) h0)
  have he : Even (familyLayers k) := by
    refine ⟨k+2, ?_⟩
    unfold familyLayers
    omega
  dsimp [familyPrime,chosenPrime]
  rw [dif_pos h0]
  exact ⟨hL,he,hp.1,hp.2.1.le,hp.2.2⟩

private theorem finite_vertex_card (L q : ℕ) : Fintype.card (Vertex L q) = (vertices L q).card := by
  simp only [Vertex,Fintype.card_coe]

private theorem finite_edge_card (L q : ℕ) :
    (edgeSet (finiteConstruction L q)).card = (constructionEdges L q).card := by
  classical
  apply Finset.card_bij (fun e _ => (e.1.val,e.2.val))
  · intro e he
    have h := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨e.1.property,e.2.property⟩,h⟩
  · intro a ha b hb heq
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst heq)
    · exact Subtype.ext (congrArg Prod.snd heq)
  · intro e he
    have h := Finset.mem_filter.mp he
    have hv := Finset.mem_product.mp h.1
    refine ⟨(⟨e.1,hv.1⟩,⟨e.2,hv.2⟩),?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2⟩

private theorem relax_count (P L D e : ℕ)
    (hc : P*((L-1)/(D+1)) ≤ e) : P*(L-1) ≤ (e+P)*(D+1) := by
  have hd : 0 < D+1 := by omega
  have hr := Nat.mod_lt (L-1) hd
  have heq := Nat.mod_add_div (L-1) (D+1)
  have hmul := Nat.mul_le_mul_left (D+1) hc
  have hrem := Nat.mul_le_mul_left P (Nat.le_of_lt hr)
  nlinarith
theorem solution :
    Filter.Tendsto (fun k : ℕ => (Fintype.card (FamilyVertex k) : ℝ))
      Filter.atTop Filter.atTop ∧
    ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ k₀ : ℕ,
      ∀ k : ℕ, k₀ ≤ k → ∀ (W : Type) [Fintype W],
      ∀ extra : Finset ((FamilyVertex k ⊕ W) × (FamilyVertex k ⊕ W)),
        IsSteinerShortcut (familyGraph k) extra →
        (extra.card : ℝ) ≤ A * Real.rpow ((edgeSet (familyGraph k)).card : ℝ) (1+ε) →
        b * Real.rpow (Fintype.card (FamilyVertex k) : ℝ) ((1-57*ε)/56) ≤
          (diameter (augment (familyGraph k) extra) : ℝ) := by
  classical
  obtain ⟨c,C,hc,hcC,hs⟩ := equation_11
  have hC : 0 < C := hc.trans_le hcC
  have sizes (k : ℕ) := hs (familyLayers k) (familyPrime k) (family_admissible k)
  have hL (k : ℕ) : 4 ≤ (familyLayers k : ℝ) := by unfold familyLayers;push_cast;linarith [Nat.cast_nonneg (α := ℝ) k]
  have hLp (k : ℕ) : 0 < (familyLayers k : ℝ) := lt_of_lt_of_le (by norm_num) (hL k)
  have hnpos (k : ℕ) : 0 < ((vertices (familyLayers k) (familyPrime k)).card : ℝ) :=
    (mul_pos hc (pow_pos (hLp k) 56)).trans_le (sizes k).2.1.1
  have hmpos (k : ℕ) : 0 < ((constructionEdges (familyLayers k) (familyPrime k)).card : ℝ) :=
    (mul_pos hc (pow_pos (hLp k) 57)).trans_le (sizes k).2.2.2.1.1
  constructor
  · apply Filter.tendsto_atTop.mpr
    intro B
    obtain ⟨k₀,hk₀⟩ := exists_nat_gt (B/c)
    refine Filter.eventually_atTop.mpr ⟨k₀,?_⟩
    intro k hk
    rw [finite_vertex_card]
    have hL1 : 1 ≤ (familyLayers k : ℝ) := by linarith [hL k]
    have hp : (familyLayers k : ℝ) ≤ (familyLayers k : ℝ)^56 := by
      calc (familyLayers k : ℝ) = (familyLayers k : ℝ)*1^55 := by norm_num
           _ ≤ (familyLayers k : ℝ)*(familyLayers k : ℝ)^55 := by gcongr
           _ = (familyLayers k : ℝ)^56 := by ring
    have hkl : (k : ℝ) ≤ (familyLayers k : ℝ) := by unfold familyLayers;push_cast;linarith
    have hkk : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hBc : B < (k₀ : ℝ)*c := (div_lt_iff₀ hc).mp hk₀
    have hmul := mul_le_mul_of_nonneg_left (hkk.trans (hkl.trans hp)) hc.le
    linarith [(sizes k).2.1.1]
  · intro ε A hε hA
    refine ⟨lowerConstant c C ε A,lower_constant_pos c C ε A hc hC hA,0,?_⟩
    intro k hk W inst extra he hbudget
    let L := familyLayers k
    let q := familyPrime k
    let D := diameter (augment (familyGraph k) extra)
    have hcharge := construction_shortcut_tradeoff L q (family_admissible k) W extra he
    have hrelax := relax_count (criticalPaths L q).card L D extra.card hcharge.2
    have hcount : ((criticalPaths L q).card : ℝ)*((L : ℝ)-1) ≤
        ((extra.card : ℝ)+((criticalPaths L q).card : ℝ))*((D : ℝ)+1) := by
      have h1 : 1 ≤ L := by have hh:4 ≤ L := (family_admissible k).1;omega
      exact_mod_cast hrelax
    have hn : (1 : ℝ) ≤ ((vertices L q).card : ℝ) := by
      have hh : 0 < (vertices L q).card := by exact_mod_cast hnpos k
      exact_mod_cast hh
    have hm : (1 : ℝ) ≤ ((constructionEdges L q).card : ℝ) := by
      have hh : 0 < (constructionEdges L q).card := by exact_mod_cast hmpos k
      exact_mod_cast hh
    have hD : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcharge.1
    have hbudget' : (extra.card : ℝ) ≤ A * Real.rpow ((constructionEdges L q).card : ℝ) (1+ε) := by
      simpa only [familyGraph,finite_edge_card] using hbudget
    have hh := diameter_power_bound c C ε A (L : ℝ)
      ((vertices L q).card : ℝ) ((constructionEdges L q).card : ℝ)
      ((criticalPaths L q).card : ℝ) (extra.card : ℝ) (D : ℝ)
      hc hC hε hA (hL k) hn hm (Nat.cast_nonneg _) hD
      (sizes k).2.2.2.2.2.1.1 (sizes k).2.2.2.2.2.1.2
      (sizes k).2.1.2 (sizes k).2.2.2.1.2 hcount hbudget'
    simpa only [rateExponent,finite_vertex_card,Real.rpow_eq_pow] using hh

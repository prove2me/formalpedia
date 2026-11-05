-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.meets_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:22:01.990263+00:00
-- url     : https://prove2.me/submissions/ba6c2453-2055-4766-a253-dc7bd3fd61ed

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenMain
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_88b09a412b2c33a9
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_lt_pow_two
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_lowerCode_eq_update
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_high_step
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_low_step
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_abs
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_succ
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryQuery_update_below
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_bank_exit_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_branches_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_memo_exit_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_queryTime_lookup
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_queryTime_step
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_step_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_digitCost_eq
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_cost_update_drop
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_digitCost_eq
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_digits



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedFrozenQueryCost (cacheCost cost_update_drop)
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution {N pMain pLookup pDigit pZero pErase : ℕ}
    (hmain : P[pMain]?=some (body pMain pLookup pDigit pZero pErase))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (T bankCodes bankCount bankValues nearCodes nearCount nearValues powers L U : ℕ)
    (H : TritWord N→ℤ) (Q : TritWord N) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcutWord : (T : ℤ)+1≤lim.word)
    (hvalueWord : 4*((4^N : ℕ) : ℤ)*(U : ℤ)+3≤lim.word)
    (hpowers : Powers μ powers (2*N))
    (hH : ∀ R, |H R|≤(U : ℤ))
    (hargs : ∀ K≤N, ∀ R : TritWord N,
      ∀ x∈inputs N K (cacheCost R) T (address R) bankCodes bankCount bankValues
        nearCodes nearCount nearValues powers L, |x|≤lim.word)
    (hbankLeaf : ∀ K≤N, ∀ R : TritWord N, Below R Q → cacheCost R≤T →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [bankCodes,bankCount,address R,bankValues,powers,L,K] μ
        (LightTernaryQueryLookup.time L)
        (fun v μ' => v=stageValue K H R ∧ μ'=μ))
    (hnearLeaf : ∀ R : TritWord N, Below R Q → T<cacheCost R →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [nearCodes,nearCount,address R,nearValues,powers,L,0] μ
        (LightTernaryQueryLookup.time L)
        (fun v μ' => v=H R ∧ μ'=μ)) :
    ∀ K≤N, ∀ R : TritWord N, Below R Q → ∀ d, d+K+2*N+L+3≤lim.depth →
      Meets lim P pMain d
        (inputs N K (cacheCost R) T (address R) bankCodes bankCount bankValues
          nearCodes nearCount nearValues powers L) μ (queryTime L T K R)
        (fun v μ' => v=stageValue K H R ∧ μ'=μ) := by
  have hone : 1≤lim.word := by omega
  have hBnonneg : 0≤((4^N : ℕ) : ℤ)*(U : ℤ) := by positivity
  have hBword : ((4^N : ℕ) : ℤ)*(U : ℤ)≤lim.word := by nlinarith
  have hbound (K : ℕ) (hKN : K≤N) (R : TritWord N) :
      |stageValue K H R|≤((4^N : ℕ) : ℤ)*(U : ℤ) := by
    have hs := stageValue_abs K hKN H U hH R
    have hp : ((4^K : ℕ) : ℤ)≤((4^N : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤4) hKN
    exact hs.trans (mul_le_mul_of_nonneg_right hp (by positivity))
  intro K
  induction K with
  | zero =>
    intro hKN R hRQ d hd
    by_cases hb : cacheCost R≤T
    · have hl := hbankLeaf 0 hKN R hRQ hb (d+1) (by omega)
      exact (bank_exit_meets hmain N 0 (cacheCost R) T bankCodes bankCount bankValues nearCodes
        nearCount nearValues powers L (address R) (stageValue 0 H R) μ hb hone hcutWord
        (hargs 0 hKN R) (by omega) hl).mono_time
        ((queryTime_lookup L T 0 R).trans' (by omega))
    · have hl := hnearLeaf R hRQ (by omega) (d+1) (by omega)
      simpa only [stageValue_zero] using
        (memo_exit_meets hmain N (cacheCost R) T bankCodes bankCount bankValues nearCodes
          nearCount nearValues powers L (address R) (H R) μ (by omega) hone hcutWord
          (hargs 0 hKN R) (by omega) hl).mono_time (queryTime_lookup L T 0 R)
  | succ K ih =>
    intro hKN R hRQ d hd
    by_cases hb : cacheCost R≤T
    · have hl := hbankLeaf (K+1) hKN R hRQ hb (d+1) (by omega)
      exact (bank_exit_meets hmain N (K+1) (cacheCost R) T bankCodes bankCount bankValues nearCodes
        nearCount nearValues powers L (address R) (stageValue (K+1) H R) μ hb hone hcutWord
        (hargs (K+1) hKN R) (by omega) hl).mono_time
        ((queryTime_lookup L T (K+1) R).trans' (by omega))
    · have hK : K<N := by omega
      let i : Fin N :=⟨K,hK⟩
      let q : Fin 3 :=R i
      let c0 : ℕ :=LightTernaryCodes.zeroCode (2*N) (2*(N-(K+1))) (2*(N-(K+1))+1) (address R)
      let c1 : ℕ :=LightTernaryCodes.oneCode (2*N) (2*(N-(K+1))+1) (address R)
      let f : Fin 3→ℤ :=fun r => stageValue K H (Function.update R i r)
      let t : Fin 3→ℕ :=fun r => if r≤q then queryTime L T K (Function.update R i r) else 0
      have hlow : low i=2*(N-(K+1)) := low_step hK
      have hhigh : high i=2*(N-(K+1))+1 := high_step hK
      have hcode (r : Fin 3) (hr : r≤q) :
          (if r=0 then (c0 : ℤ) else if r=1 then (c1 : ℤ) else (address R : ℤ))=
            (address (Function.update R i r) : ℤ) := by
        have hc := lowerCode_eq_update R i r hr
        simp only [lowerCode,hlow,hhigh] at hc
        dsimp only [c0,c1]
        split_ifs at hc ⊢ <;> exact_mod_cast hc
      have hchildren : ∀ r : Fin 3, r≤q →
          Meets lim P pMain (d+1)
            (inputs N K (cacheCost R-(digitCost q.val-digitCost r.val)) T
              (if r=0 then (c0 : ℤ) else if r=1 then (c1 : ℤ) else (address R : ℤ))
              bankCodes bankCount bankValues nearCodes nearCount nearValues powers L) μ (t r)
            (fun v μ' => v=f r ∧ μ'=μ) := by
        intro r hr
        have hchildRQ : Below (Function.update R i r) Q := by
          intro j
          exact (update_below R i r hr j).trans (hRQ j)
        have hc := ih (by omega) (Function.update R i r) hchildRQ (d+1) (by omega)
        simpa only [t,if_pos hr,f,cost_update_drop R i r hr,q,hcode r hr] using hc
      have hargsPrepared : ∀ x∈preparedInputs N K (cacheCost R) T (address R) bankCodes bankCount bankValues
          nearCodes nearCount nearValues powers L q c0 c1, |x|≤lim.word := by
        intro x hx
        simp only [preparedInputs,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
        rcases hx with hx|hx
        · exact hargs (K+1) hKN R x hx
        · rcases hx with rfl|rfl|rfl|rfl
          · have hq : q.val≤2 := by omega
            rw [abs_of_nonneg (by positivity : (0 : ℤ)≤q.val)]
            omega
          · have hc := ThreeSum.MaskErase.eraseMask_le
              ((ThreeSum.MaskErase.eraseMask_le (a := 2*(N-(K+1))+1) (address_lt_pow_two R)).trans_lt
                (address_lt_pow_two R)) (a := 2*(N-(K+1)))
            have hm := address_lt_pow_two R
            unfold c0 LightTernaryCodes.zeroCode
            rw [abs_of_nonneg (by positivity)]
            have hz : (LightTernaryCodes.zeroCode (2*N) (2*(N-(K+1))) (2*(N-(K+1))+1) (address R) : ℤ)≤
                (address R : ℤ) := by
              have hh := ThreeSum.MaskErase.eraseMask_le (a := 2*(N-(K+1))+1) hm
              exact_mod_cast hc.trans hh
            exact hz.trans (abs_le.mp (hargs (K+1) hKN R (address R) (by simp [inputs]))).2
          · have hm := address_lt_pow_two R
            have hc := ThreeSum.MaskErase.eraseMask_le (a := 2*(N-(K+1))+1) hm
            unfold c1 LightTernaryCodes.oneCode
            rw [abs_of_nonneg (by positivity)]
            exact (by exact_mod_cast hc :
              (ThreeSum.MaskErase.eraseMask (2*N) (2*(N-(K+1))+1) (address R) : ℤ)≤address R).trans
              (abs_le.mp (hargs (K+1) hKN R (address R) (by simp [inputs]))).2
          · exact hargs K (by omega) R K (by simp [inputs])
      have hchildbound : ∀ r, |f r|≤((4^N : ℕ) : ℤ)*(U : ℤ) :=fun r => hbound K (by omega) _
      have hbranchWord : 4*max (|f 0|) (max (|f 1|) (|f 2|))+3≤lim.word := by
        have hm := max_le (hchildbound 0) (max_le (hchildbound 1) (hchildbound 2))
        nlinarith
      have hqrank : digitCost q.val≤cacheCost R := by
        change digitCost (R i).val≤WeightedCache.cost WeightedFrozenQueryCost.c R
        rw [WeightedFrozenQueryCost.digitCost_eq]
        exact Finset.single_le_sum (fun j _ => Nat.zero_le (WeightedFrozenQueryCost.c (R j))) (Finset.mem_univ i)
      have hbr := branches_meets N K (cacheCost R) T bankCodes bankCount bankValues nearCodes nearCount nearValues
        powers L (address R) c0 c1 q f t μ hargsPrepared hbranchWord hqrank (by omega) hchildren
      have hvalue : stageValue (K+1) H R=inverseDigit f q := stageValue_succ hK H R
      rw [←hvalue] at hbr
      have hdi : LightTernaryCodes.digit (2*N) (2*(N-(K+1))) (2*(N-(K+1))+1) (address R)=q.val := by
        have hh := digit_eq R i
        rw [hlow,hhigh] at hh
        exact hh
      have hm := step_meets hmain hdigit hzero herase N K (cacheCost R) T (address R) bankCodes bankCount bankValues
        nearCodes nearCount nearValues powers L q (stageValue (K+1) H R) μ hK (by omega) hw hspace hword
        hNword hcutWord hpowers (address_lt_pow_two R) (hargs (K+1) hKN R) hdi (by omega) hbr
      exact hm.mono_time (queryTime_step L T R hK (by omega))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery

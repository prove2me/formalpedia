-- Prove2me | solution 1 for PrivBayesTest.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T19:43:07.222876+00:00
-- url     : https://prove2.me/submissions/b8f4f577-4168-43e9-92c4-69f98dc6eaa5

import Mathlib
import Definitions.Def_PrivBayesTest_saddleObj
import Definitions.Def_PrivBayesTest_klTvValue

namespace SaddleBalance
open PrivBayesTest

lemma linear_max {A B c a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hm : ∀ b ∈ Set.Icc (0 : ℝ) 1,
      b * A + (1-b) * B + b * c ≤ a * A + (1-a) * B + a * c) :
    A + c = B := by
  have h0 := hm 0 (by norm_num)
  have h1 := hm 1 (by norm_num)
  simp only [zero_mul,sub_zero,one_mul,sub_self,zero_add,add_zero] at h0 h1
  have hlow : 0 ≤ A + c - B := by nlinarith [ha.1]
  have hupp : A + c - B ≤ 0 := by nlinarith [ha.2]
  linarith

lemma min_max {A B c a : ℝ} (hc : 0 ≤ c) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hm : ∀ b ∈ Set.Icc (0 : ℝ) 1,
      b * A + (1-b) * B + min b (1-b) * c ≤
        a * A + (1-a) * B + min a (1-a) * c) :
    ∃ τ ∈ Set.Icc (0 : ℝ) 1,
      a * A + (1-a) * B + min a (1-a) * c = A + τ * c ∧
      a * A + (1-a) * B + min a (1-a) * c = B + (1-τ) * c ∧
      (a ≠ 1/2 → τ = 0 ∨ τ = 1) := by
  have h0 := hm 0 (by norm_num)
  have h1 := hm 1 (by norm_num)
  have hh := hm (1/2) (by norm_num)
  norm_num at h0 h1 hh
  rcases lt_trichotomy a (1/2) with hl | he | hr
  · rw [min_eq_left (by linarith)] at h0 h1 hh ⊢
    have heq : A + c = B := by
      have hlow : 0 ≤ A + c - B := by nlinarith [ha.1]
      have hupp : A + c - B ≤ 0 := by nlinarith
      linarith
    refine ⟨1,by norm_num,?_,?_,by simp⟩ <;> nlinarith
  · subst a
    norm_num at h0 h1 hh
    simp only [show min (1 / 2 : ℝ) (1 - 1 / 2) = 1/2 by norm_num]
    by_cases hz : c = 0
    · subst c
      have heq : A = B := by linarith
      subst A
      exact ⟨0,by norm_num,by ring,by ring,by simp⟩
    · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm hz)
      refine ⟨(B+c-A)/(2*c),?_,?_,?_,by simp⟩
      · constructor
        · apply div_nonneg <;> linarith
        · apply (div_le_one (by positivity)).mpr
          linarith
      · field_simp
        <;> ring
      · field_simp
        <;> ring
  · rw [min_eq_right (by linarith)] at h0 h1 hh ⊢
    have heq : B + c = A := by
      have hlow : 0 ≤ B + c - A := by nlinarith [ha.2]
      have hupp : B + c - A ≤ 0 := by nlinarith
      linarith
    refine ⟨0,by norm_num,?_,?_,by simp⟩ <;> nlinarith

lemma balancing {E : Type*} (ε : ℝ) (hε : 0 < ε) (ω : ℝ → ℝ)
    (hω : ω = alphaTilde ∨ ω = id) (A B W : E → ℝ) (z : E) (hW : 0 ≤ W z)
    (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hm : ∀ b ∈ Set.Icc (0 : ℝ) 1, saddleObj ω ε A B W b z ≤ saddleObj ω ε A B W a z) :
    ∃ τ ∈ Set.Icc (0 : ℝ) 1,
      saddleObj ω ε A B W a z = A z + τ * ε * W z ∧
      saddleObj ω ε A B W a z = B z + (1-τ) * ε * W z ∧
      (ω = alphaTilde → a ≠ 1/2 → τ = 0 ∨ τ = 1) ∧ (ω = id → τ = 1) := by
  have hneq : alphaTilde ≠ (id : ℝ → ℝ) := by
    intro h
    have hh := congrFun h 1
    norm_num [alphaTilde] at hh
  rcases hω with rfl | rfl
  · obtain ⟨τ,hτ,he1,he2,he3⟩ := min_max (mul_nonneg hε.le hW) ha
      (by simpa [saddleObj,alphaTilde,mul_assoc] using hm)
    refine ⟨τ,hτ,?_,?_,fun _ => he3,fun hh => (hneq hh).elim⟩
    · simpa [saddleObj,alphaTilde,mul_assoc] using he1
    · simpa [saddleObj,alphaTilde,mul_assoc] using he2
  · have he := linear_max ha (by simpa [saddleObj,mul_assoc] using hm)
    refine ⟨1,by norm_num,?_,?_,fun hh => (hneq hh.symm).elim,by simp⟩
    · simp only [saddleObj,id_eq,one_mul]
      rw [← he]
      ring
    · simp only [saddleObj,id_eq,sub_self,zero_mul,add_zero]
      rw [← he]
      ring

lemma value {E : Type*} (Z : Set E) (f : ℝ → E → ℝ) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (z : E) (hz : z ∈ Z) (hmin : ∀ y ∈ Z, f a z ≤ f a y)
    (hmax : ∀ b ∈ Set.Icc (0 : ℝ) 1, f b z ≤ f a z) :
    (f a z : EReal) = ⨆ b ∈ Set.Icc (0 : ℝ) 1, ⨅ y ∈ Z, (f b y : EReal) := by
  apply le_antisymm
  · apply le_iSup_of_le a
    apply le_iSup_of_le ha
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact_mod_cast hmin y hy
  · apply iSup_le
    intro b
    apply iSup_le
    intro hb
    apply (iInf_le_of_le z (iInf_le_of_le hz le_rfl)).trans
    exact_mod_cast hmax b hb

end SaddleBalance

universe u_1
theorem projected_consequences : (
  ∀ {E : Type u_1} [inst : AddCommGroup E]
    [inst_1 : @_root_.Module Real E Real.semiring (@AddCommGroup.toAddCommMonoid E inst)] [inst_2 : TopologicalSpace E]
    (ε : Real),
    @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) ε →
      ∀ (ω : Real → Real),
        Or (@Eq (Real → Real) ω PrivBayesTest.alphaTilde) (@Eq (Real → Real) ω (@id Real)) →
          ∀ (Z : Set E),
            @Convex Real E Real.semiring Real.partialOrder (@AddCommGroup.toAddCommMonoid E inst)
                (@SMulZeroClass.toSMul Real E
                  (@AddZero.toZero E
                    (@AddZeroClass.toAddZero E
                      (@AddMonoid.toAddZeroClass E
                        (@SubNegMonoid.toAddMonoid E (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))))
                  (@DistribSMul.toSMulZeroClass Real E
                    (@AddMonoid.toAddZeroClass E
                      (@SubNegMonoid.toAddMonoid E (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))
                    (@DistribMulAction.toDistribSMul Real E Real.instMonoid
                      (@SubNegMonoid.toAddMonoid E (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst)))
                      (@Module.toDistribMulAction Real E Real.semiring (@AddCommGroup.toAddCommMonoid E inst) inst_1))))
                Z →
              @Set.Nonempty E Z →
                ∀ (A B W : E → Real),
                  (∀ (z : E),
                      @Membership.mem E (Set E) (@Set.instMembership E) Z z →
                        @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                          (A z)) →
                    (∀ (z : E),
                        @Membership.mem E (Set E) (@Set.instMembership E) Z z →
                          @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                            (B z)) →
                      (∀ (z : E),
                          @Membership.mem E (Set E) (@Set.instMembership E) Z z →
                            @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                              (W z)) →
                        @ConvexOn Real E Real Real.semiring Real.partialOrder (@AddCommGroup.toAddCommMonoid E inst)
                            Real.instAddCommMonoid Real.partialOrder
                            (@SMulZeroClass.toSMul Real E
                              (@AddZero.toZero E
                                (@AddZeroClass.toAddZero E
                                  (@AddMonoid.toAddZeroClass E
                                    (@SubNegMonoid.toAddMonoid E
                                      (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))))
                              (@DistribSMul.toSMulZeroClass Real E
                                (@AddMonoid.toAddZeroClass E
                                  (@SubNegMonoid.toAddMonoid E
                                    (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))
                                (@DistribMulAction.toDistribSMul Real E Real.instMonoid
                                  (@SubNegMonoid.toAddMonoid E
                                    (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst)))
                                  (@Module.toDistribMulAction Real E Real.semiring (@AddCommGroup.toAddCommMonoid E inst)
                                    inst_1))))
                            (@instSMulOfMul Real Real.instMul) Z A →
                          @ConvexOn Real E Real Real.semiring Real.partialOrder (@AddCommGroup.toAddCommMonoid E inst)
                              Real.instAddCommMonoid Real.partialOrder
                              (@SMulZeroClass.toSMul Real E
                                (@AddZero.toZero E
                                  (@AddZeroClass.toAddZero E
                                    (@AddMonoid.toAddZeroClass E
                                      (@SubNegMonoid.toAddMonoid E
                                        (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))))
                                (@DistribSMul.toSMulZeroClass Real E
                                  (@AddMonoid.toAddZeroClass E
                                    (@SubNegMonoid.toAddMonoid E
                                      (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))
                                  (@DistribMulAction.toDistribSMul Real E Real.instMonoid
                                    (@SubNegMonoid.toAddMonoid E
                                      (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst)))
                                    (@Module.toDistribMulAction Real E Real.semiring
                                      (@AddCommGroup.toAddCommMonoid E inst) inst_1))))
                              (@instSMulOfMul Real Real.instMul) Z B →
                            @ConvexOn Real E Real Real.semiring Real.partialOrder (@AddCommGroup.toAddCommMonoid E inst)
                                Real.instAddCommMonoid Real.partialOrder
                                (@SMulZeroClass.toSMul Real E
                                  (@AddZero.toZero E
                                    (@AddZeroClass.toAddZero E
                                      (@AddMonoid.toAddZeroClass E
                                        (@SubNegMonoid.toAddMonoid E
                                          (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))))
                                  (@DistribSMul.toSMulZeroClass Real E
                                    (@AddMonoid.toAddZeroClass E
                                      (@SubNegMonoid.toAddMonoid E
                                        (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))
                                    (@DistribMulAction.toDistribSMul Real E Real.instMonoid
                                      (@SubNegMonoid.toAddMonoid E
                                        (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst)))
                                      (@Module.toDistribMulAction Real E Real.semiring
                                        (@AddCommGroup.toAddCommMonoid E inst) inst_1))))
                                (@instSMulOfMul Real Real.instMul) Z W →
                              @LowerSemicontinuousOn E Real inst_2 Real.instPreorder A Z →
                                @LowerSemicontinuousOn E Real inst_2 Real.instPreorder B Z →
                                  @LowerSemicontinuousOn E Real inst_2 Real.instPreorder W Z →
                                    (∀ (t : Real),
                                        @IsCompact E inst_2
                                          (@Set.ofPred E fun (z : E) =>
                                            And (@Membership.mem E (Set E) (@Set.instMembership E) Z z)
                                              (∀ (α : Real),
                                                @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                    (@Set.Icc Real Real.instPreorder
                                                      (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                                                      (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                                    α →
                                                  @LE.le Real Real.instLE (@PrivBayesTest.saddleObj E ω ε A B W α z)
                                                    t))) →
                                      ∀ (α₀ : Real),
                                        @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                            (@Set.Icc Real Real.instPreorder
                                              (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                                              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                            α₀ →
                                          ∀ (z₀ : E),
                                            @Membership.mem E (Set E) (@Set.instMembership E) Z z₀ →
                                              (∀ (z : E),
                                                  @Membership.mem E (Set E) (@Set.instMembership E) Z z →
                                                    @LE.le Real Real.instLE (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)
                                                      (@PrivBayesTest.saddleObj E ω ε A B W α₀ z)) →
                                                (∀ (α : Real),
                                                    @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                        (@Set.Icc Real Real.instPreorder
                                                          (@OfNat.ofNat Real (nat_lit 0)
                                                            (@Zero.toOfNat0 Real Real.instZero))
                                                          (@OfNat.ofNat Real (nat_lit 1)
                                                            (@One.toOfNat1 Real Real.instOne)))
                                                        α →
                                                      @LE.le Real Real.instLE (@PrivBayesTest.saddleObj E ω ε A B W α z₀)
                                                        (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)) →
                                                  And
                                                    (@Eq EReal (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀).toEReal
                                                      (⨆ (α : Real),
                                                        ⨆ (_ :
                                                          @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                            (@Set.Icc Real Real.instPreorder
                                                              (@OfNat.ofNat Real (nat_lit 0)
                                                                (@Zero.toOfNat0 Real Real.instZero))
                                                              (@OfNat.ofNat Real (nat_lit 1)
                                                                (@One.toOfNat1 Real Real.instOne)))
                                                            α),
                                                          ⨅ (z : E),
                                                            ⨅ (_ : @Membership.mem E (Set E) (@Set.instMembership E) Z z),
                                                              (@PrivBayesTest.saddleObj E ω ε A B W α z).toEReal))
                                                    (@Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                        (@Set.Ioo Real Real.instPreorder
                                                          (@OfNat.ofNat Real (nat_lit 0)
                                                            (@Zero.toOfNat0 Real Real.instZero))
                                                          (@OfNat.ofNat Real (nat_lit 1)
                                                            (@One.toOfNat1 Real Real.instOne)))
                                                        α₀ →
                                                      ∃ (τ : Real),
                                                        And
                                                          (@Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                            (@Set.Icc Real Real.instPreorder
                                                              (@OfNat.ofNat Real (nat_lit 0)
                                                                (@Zero.toOfNat0 Real Real.instZero))
                                                              (@OfNat.ofNat Real (nat_lit 1)
                                                                (@One.toOfNat1 Real Real.instOne)))
                                                            τ)
                                                          (And
                                                            (@Eq Real (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)
                                                              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                                                                (A z₀)
                                                                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                                                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                                                    τ ε)
                                                                  (W z₀))))
                                                            (And
                                                              (@Eq Real (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)
                                                                (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                                                                  (B z₀)
                                                                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                                                    (@HMul.hMul Real Real Real
                                                                      (@instHMul Real Real.instMul)
                                                                      (@HSub.hSub Real Real Real
                                                                        (@instHSub Real Real.instSub)
                                                                        (@OfNat.ofNat Real (nat_lit 1)
                                                                          (@One.toOfNat1 Real Real.instOne))
                                                                        τ)
                                                                      ε)
                                                                    (W z₀))))
                                                              (And
                                                                (@Eq (Real → Real) ω PrivBayesTest.alphaTilde →
                                                                  @Ne Real α₀
                                                                      (@HDiv.hDiv Real Real Real
                                                                        (@instHDiv Real
                                                                          (@DivInvMonoid.toDiv Real
                                                                            Real.instDivInvMonoid))
                                                                        (@OfNat.ofNat Real (nat_lit 1)
                                                                          (@One.toOfNat1 Real Real.instOne))
                                                                        (@OfNat.ofNat Real (nat_lit 2)
                                                                          (@instOfNatAtLeastTwo Real (nat_lit 2)
                                                                            Real.instNatCast
                                                                            (@Nat.instAtLeastTwoHAddOfNat
                                                                              (@OfNat.ofNat Nat (nat_lit 1)
                                                                                (instOfNatNat (nat_lit 1)))
                                                                              (@Nat.instNeZeroSucc
                                                                                (@OfNat.ofNat Nat (nat_lit 0)
                                                                                  (instOfNatNat (nat_lit 0)))))))) →
                                                                    Or
                                                                      (@Eq Real τ
                                                                        (@OfNat.ofNat Real (nat_lit 0)
                                                                          (@Zero.toOfNat0 Real Real.instZero)))
                                                                      (@Eq Real τ
                                                                        (@OfNat.ofNat Real (nat_lit 1)
                                                                          (@One.toOfNat1 Real Real.instOne))))
                                                                (@Eq (Real → Real) ω (@id Real) →
                                                                  @Eq Real τ
                                                                    (@OfNat.ofNat Real (nat_lit 1)
                                                                      (@One.toOfNat1 Real Real.instOne)))))))
) := by
  intro E instAdd instMod instTop ε hε ω hω Z hZ hZne A B W hA0 hB0 hW0 hAc hBc hWc hAl hBl hWl hcpt
  intro a ha z hz hmin hmax
  constructor
  · exact SaddleBalance.value Z (PrivBayesTest.saddleObj ω ε A B W) a ha z hz hmin hmax
  · intro hai
    exact SaddleBalance.balancing ε hε ω hω A B W z (hW0 z hz) a hai hmax

-- At an endpoint, maximization alone does not imply the balancing equalities.
theorem endpoint_control :
    (∀ b ∈ Set.Icc (0 : ℝ) 1, 1-b ≤ 1) ∧
      ¬ (∃ τ : ℝ, (1 : ℝ) = 0 + τ * 0 ∧ (1 : ℝ) = 1 + (1-τ)*0) := by
  constructor
  · intro b hb
    linarith [hb.1]
  · norm_num

-- The kink can require a non-endpoint choice of τ.
theorem kink_control :
    (∀ b ∈ Set.Icc (0 : ℝ) 1, min b (1-b) ≤ (1/2 : ℝ)) ∧
      (∀ τ : ℝ, (1/2 : ℝ) = τ → τ ≠ 0 ∧ τ ≠ 1) := by
  constructor
  · intro b hb
    rcases le_total b (1/2) with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  · intro τ ht
    constructor <;> linarith

namespace SaddleBalance
open PrivBayesTest

lemma exists_min_of_compact_sublevels {E : Type*} [TopologicalSpace E] (Z : Set E)
    (hne : Z.Nonempty) (f : E → ℝ) (hf : LowerSemicontinuousOn f Z)
    (hk : ∀ t : ℝ, IsCompact {z ∈ Z | f z ≤ t}) :
    ∃ z ∈ Z, ∀ y ∈ Z, f z ≤ f y := by
  obtain ⟨w,hw⟩ := hne
  have hl : LowerSemicontinuousOn f {z ∈ Z | f z ≤ f w} := hf.mono (fun _ h => h.1)
  obtain ⟨z,hz,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (show {z ∈ Z | f z ≤ f w}.Nonempty from ⟨w,hw,le_rfl⟩) (hk (f w)) hl
  refine ⟨z,hz.1,fun y hy => ?_⟩
  by_cases h : f y ≤ f w
  · exact hmin ⟨hy,h⟩
  · exact hz.2.trans (le_of_not_ge h)

lemma three_point_bound (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id)
    (A B c t : ℝ) (h0 : B ≤ t) (hh : (A+B+c)/2 ≤ t) (h1 : A ≤ t)
    (hi : A+c ≤ t) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    a*A+(1-a)*B+ω a*c ≤ t := by
  rcases hω with rfl | rfl
  · unfold alphaTilde
    rcases le_total a (1/2) with h | h
    · rw [min_eq_left (by linarith)]
      nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hh),
        mul_nonneg (show 0 ≤ 1-2*a by linarith) (sub_nonneg.mpr h0)]
    · rw [min_eq_right (by linarith)]
      nlinarith [mul_nonneg (show 0 ≤ 1-a by linarith [ha.2]) (sub_nonneg.mpr hh),
        mul_nonneg (show 0 ≤ 2*a-1 by linarith) (sub_nonneg.mpr h1)]
  · simp only [id_eq]
    nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hi),
      mul_nonneg (show 0 ≤ 1-a by linarith [ha.2]) (sub_nonneg.mpr h0)]

lemma bound_by_three_samples {E : Type*} (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id)
    (ε : ℝ) (A B W : E → ℝ) (z : E) (t : ℝ)
    (h0 : saddleObj ω ε A B W 0 z ≤ t)
    (hh : saddleObj ω ε A B W (1/2) z ≤ t)
    (h1 : saddleObj ω ε A B W 1 z ≤ t) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, saddleObj ω ε A B W a z ≤ t := by
  intro a ha
  rcases hω with rfl | rfl
  · norm_num [saddleObj,alphaTilde] at h0 hh h1
    unfold saddleObj alphaTilde
    rcases le_total a (1/2) with h | h
    · rw [min_eq_left (by linarith)]
      nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hh),
        mul_nonneg (show 0 ≤ 1-2*a by linarith) (sub_nonneg.mpr h0)]
    · rw [min_eq_right (by linarith)]
      nlinarith [mul_nonneg (show 0 ≤ 1-a by linarith [ha.2]) (sub_nonneg.mpr hh),
        mul_nonneg (show 0 ≤ 2*a-1 by linarith) (sub_nonneg.mpr h1)]
  · norm_num [saddleObj] at h0 h1
    simp only [saddleObj,id_eq]
    nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr h1),
      mul_nonneg (show 0 ≤ 1-a by linarith [ha.2]) (sub_nonneg.mpr h0)]

lemma objective_lsc {E : Type*} [TopologicalSpace E] (Z : Set E) (ε : ℝ) (hε : 0 ≤ ε)
    (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id) (A B W : E → ℝ)
    (hA : LowerSemicontinuousOn A Z) (hB : LowerSemicontinuousOn B Z)
    (hW : LowerSemicontinuousOn W Z) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    LowerSemicontinuousOn (saddleObj ω ε A B W a) Z := by
  have scale (f : E → ℝ) (hf : LowerSemicontinuousOn f Z) (c : ℝ) (hc : 0 ≤ c) :
      LowerSemicontinuousOn (fun x => c*f x) Z :=
    (continuous_const.mul continuous_id).comp_lowerSemicontinuousOn hf
      (fun _ _ h => mul_le_mul_of_nonneg_left h hc)
  have hw : 0 ≤ ω a := by
    rcases hω with rfl | rfl
    · exact le_min ha.1 (sub_nonneg.mpr ha.2)
    · exact ha.1
  exact ((scale A hA a ha.1).add (scale B hB (1-a) (sub_nonneg.mpr ha.2))).add
    (scale W hW (ω a*ε) (mul_nonneg hw hε))

lemma minimax_attained {E : Type*} [TopologicalSpace E] (Z : Set E) (hne : Z.Nonempty)
    (ε : ℝ) (hε : 0 ≤ ε) (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id)
    (A B W : E → ℝ) (hA : LowerSemicontinuousOn A Z) (hB : LowerSemicontinuousOn B Z)
    (hW : LowerSemicontinuousOn W Z)
    (hk : ∀ t : ℝ, IsCompact {z ∈ Z | ∀ a ∈ Set.Icc (0 : ℝ) 1, saddleObj ω ε A B W a z ≤ t}) :
    ∃ z ∈ Z, ∀ y ∈ Z,
      max (saddleObj ω ε A B W 0 z)
        (max (saddleObj ω ε A B W (1/2) z) (saddleObj ω ε A B W 1 z)) ≤
      max (saddleObj ω ε A B W 0 y)
        (max (saddleObj ω ε A B W (1/2) y) (saddleObj ω ε A B W 1 y)) := by
  let g := fun z => max (saddleObj ω ε A B W 0 z)
    (max (saddleObj ω ε A B W (1/2) z) (saddleObj ω ε A B W 1 z))
  apply exists_min_of_compact_sublevels Z hne g
  · exact (objective_lsc Z ε hε ω hω A B W hA hB hW 0 (by norm_num)).sup
      ((objective_lsc Z ε hε ω hω A B W hA hB hW (1/2) (by norm_num)).sup
      (objective_lsc Z ε hε ω hω A B W hA hB hW 1 (by norm_num)))
  · intro t
    have heq : {z ∈ Z | g z ≤ t} =
        {z ∈ Z | ∀ a ∈ Set.Icc (0 : ℝ) 1, saddleObj ω ε A B W a z ≤ t} := by
      ext z
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hz,hg⟩
        have hh : saddleObj ω ε A B W 0 z ≤ t ∧
            saddleObj ω ε A B W (1/2) z ≤ t ∧ saddleObj ω ε A B W 1 z ≤ t := by
          simpa only [g,max_le_iff] using hg
        exact ⟨hz,bound_by_three_samples ω hω ε A B W z t hh.1 hh.2.1 hh.2.2⟩
      · rintro ⟨hz,h⟩
        exact ⟨hz,max_le (h 0 (by norm_num)) (max_le (h (1/2) (by norm_num)) (h 1 (by norm_num)))⟩
    rw [heq]
    exact hk t

end SaddleBalance

open PrivBayesTest
namespace SaddleLift
noncomputable section

def lin (ω : ℝ → ℝ) (ε a : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  a*v 0+(1-a)*v 1+ω a*ε*v 2

def upperImage {E : Type*} (Z : Set E) (A B W : E → ℝ) : Set (Fin 3 → ℝ) :=
  {v | ∃ z ∈ Z, A z ≤ v 0 ∧ B z ≤ v 1 ∧ W z ≤ v 2}

lemma image_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Z : Set E) (A B W : E → ℝ) (ha : ConvexOn ℝ Z A)
    (hb : ConvexOn ℝ Z B) (hw : ConvexOn ℝ Z W) :
    Convex ℝ (upperImage Z A B W) := by
  rintro v ⟨x,hx,hax,hbx,hwx⟩ u ⟨y,hy,hay,hby,hwy⟩ a b ha0 hb0 hab
  refine ⟨a • x+b • y,ha.1 hx hy ha0 hb0 hab,?_,?_,?_⟩
  · exact (ha.2 hx hy ha0 hb0 hab).trans (add_le_add
      (mul_le_mul_of_nonneg_left hax ha0) (mul_le_mul_of_nonneg_left hay hb0))
  · exact (hb.2 hx hy ha0 hb0 hab).trans (add_le_add
      (mul_le_mul_of_nonneg_left hbx ha0) (mul_le_mul_of_nonneg_left hby hb0))
  · exact (hw.2 hx hy ha0 hb0 hab).trans (add_le_add
      (mul_le_mul_of_nonneg_left hwx ha0) (mul_le_mul_of_nonneg_left hwy hb0))

lemma omega_nonneg (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id)
    {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) : 0 ≤ ω a := by
  rcases hω with rfl | rfl
  · exact le_min ha.1 (sub_nonneg.mpr ha.2)
  · exact ha.1

lemma omega_concave (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) 1) ω := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rcases hω with rfl | rfl
  · unfold alphaTilde
    apply le_min
    · nlinarith [mul_le_mul_of_nonneg_left (min_le_left x (1-x)) ha,
        mul_le_mul_of_nonneg_left (min_le_left y (1-y)) hb]
    · nlinarith [mul_le_mul_of_nonneg_left (min_le_right x (1-x)) ha,
        mul_le_mul_of_nonneg_left (min_le_right y (1-y)) hb]
  · rfl

lemma neg_lin_convex (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id)
    (ε : ℝ) (hε : 0 ≤ ε) (v : Fin 3 → ℝ) (hv : 0 ≤ v 2) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun a => -lin ω ε a v) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := mul_le_mul_of_nonneg_right ((omega_concave ω hω).2 hx hy ha hb hab)
    (mul_nonneg hε hv)
  simp only [smul_eq_mul] at hh ⊢
  dsimp [lin]
  nlinarith [congrArg (fun t : ℝ => t*v 1) hab]

lemma neg_lin_concave (ω : ℝ → ℝ) (ε a : ℝ) (Y : Set (Fin 3 → ℝ)) (hY : Convex ℝ Y) :
    ConcaveOn ℝ Y (fun v => -lin ω ε a v) := by
  refine ⟨hY,?_⟩
  intro v hv u hu b c hb hc hbc
  simp only [lin,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith

lemma continuous_left (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id) (ε : ℝ) (v : Fin 3 → ℝ) :
    Continuous (fun a => -lin ω ε a v) := by
  rcases hω with rfl | rfl <;> simp only [lin,alphaTilde,id_eq] <;> fun_prop

lemma continuous_right (ω : ℝ → ℝ) (ε a : ℝ) :
    Continuous (fun v => -lin ω ε a v) := by unfold lin; fun_prop

lemma image_mono {E : Type*} (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id)
    (ε : ℝ) (hε : 0 ≤ ε) (A B W : E → ℝ) (z : E) (v : Fin 3 → ℝ)
    (hA : A z ≤ v 0) (hB : B z ≤ v 1) (hW : W z ≤ v 2)
    (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) : saddleObj ω ε A B W a z ≤ lin ω ε a v := by
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hA ha.1)
    (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr ha.2)))
    (mul_le_mul_of_nonneg_left hW (mul_nonneg (omega_nonneg ω hω ha) hε))
end
end SaddleLift

namespace SaddleLift
open PrivBayesTest
noncomputable section

lemma max_witness {E : Type*} (ω : ℝ → ℝ) (ε : ℝ) (A B W : E → ℝ) (z : E) :
    ∃ a ∈ Set.Icc (0:ℝ) 1, saddleObj ω ε A B W a z =
      max (saddleObj ω ε A B W 0 z)
        (max (saddleObj ω ε A B W (1/2) z) (saddleObj ω ε A B W 1 z)) := by
  let f := fun a => saddleObj ω ε A B W a z
  change ∃ a ∈ Set.Icc (0:ℝ) 1, f a = max (f 0) (max (f (1/2)) (f 1))
  rcases le_total (f (1/2)) (f 1) with h | h
  · rw [max_eq_right h]
    rcases le_total (f 0) (f 1) with h' | h'
    · exact ⟨1,by norm_num,(max_eq_right h').symm⟩
    · exact ⟨0,by norm_num,(max_eq_left h').symm⟩
  · rw [max_eq_left h]
    rcases le_total (f 0) (f (1/2)) with h' | h'
    · exact ⟨1/2,by norm_num,(max_eq_right h').symm⟩
    · exact ⟨0,by norm_num,(max_eq_left h').symm⟩

lemma dual_at_primal {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ε : ℝ) (hε : 0 ≤ ε) (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id)
    (Z : Set E) (A B W : E → ℝ) (hW0 : ∀ z ∈ Z, 0 ≤ W z)
    (hAc : ConvexOn ℝ Z A) (hBc : ConvexOn ℝ Z B) (hWc : ConvexOn ℝ Z W)
    (z₀ : E) (hz₀ : z₀ ∈ Z)
    (hm : ∀ z ∈ Z,
      max (saddleObj ω ε A B W 0 z₀)
        (max (saddleObj ω ε A B W (1/2) z₀) (saddleObj ω ε A B W 1 z₀)) ≤
      max (saddleObj ω ε A B W 0 z)
        (max (saddleObj ω ε A B W (1/2) z) (saddleObj ω ε A B W 1 z))) :
    ∃ a ∈ Set.Icc (0:ℝ) 1,
      (∀ z ∈ Z, saddleObj ω ε A B W a z₀ ≤ saddleObj ω ε A B W a z) ∧
      (∀ b ∈ Set.Icc (0:ℝ) 1, saddleObj ω ε A B W b z₀ ≤ saddleObj ω ε A B W a z₀) := by
  let X := Set.Icc (0:ℝ) 1
  let Y := upperImage Z A B W
  let F : ℝ → (Fin 3 → ℝ) → EReal := fun a v => ((-lin ω ε a v : ℝ) : EReal)
  let value := max (saddleObj ω ε A B W 0 z₀)
    (max (saddleObj ω ε A B W (1/2) z₀) (saddleObj ω ε A B W 1 z₀))
  have hXne : X.Nonempty := ⟨0,by norm_num [X]⟩
  have hYc : Convex ℝ Y := image_convex Z A B W hAc hBc hWc
  have hfY : ∀ v ∈ Y, LowerSemicontinuousOn (fun a => F a v) X := by
    intro v hv
    exact (continuous_coe_real_ereal.comp (continuous_left ω hω ε v)).continuousOn.lowerSemicontinuousOn
  have hfYc : ∀ v ∈ Y, QuasiconvexOn ℝ X (fun a => F a v) := by
    rintro v ⟨z,hz,hA,hB,hW⟩
    convert! (neg_lin_convex ω hω ε hε v ((hW0 z hz).trans hW)).quasiconvexOn.monotone_comp
      EReal.orderEmbedding.monotone
  have hfX : ∀ a ∈ X, UpperSemicontinuousOn (fun v => F a v) Y := by
    intro a ha
    exact (continuous_coe_real_ereal.comp (continuous_right ω ε a)).continuousOn.upperSemicontinuousOn
  have hfXc : ∀ a ∈ X, QuasiconcaveOn ℝ Y (fun v => F a v) := by
    intro a ha
    convert! (neg_lin_concave ω ε a Y hYc).quasiconcaveOn.monotone_comp EReal.orderEmbedding.monotone
  have heq := Sion.minimax' hXne (convex_Icc (0:ℝ) 1) isCompact_Icc hfY hfYc hYc hfX hfXc
  have hlow : LowerSemicontinuousOn (fun a => ⨆ v ∈ Y, F a v) X := by
    intro a ha
    apply lowerSemicontinuousWithinAt_iSup
    intro v
    exact lowerSemicontinuousWithinAt_iSup fun hv => hfY v hv a ha
  obtain ⟨a,ha,hmin⟩ := hlow.exists_isMinOn hXne isCompact_Icc
  have hupper : (⨆ v ∈ Y, ⨅ a ∈ X, F a v) ≤ (-value : ℝ) := by
    apply iSup_le
    intro v
    apply iSup_le
    rintro ⟨z,hz,hA,hB,hW⟩
    obtain ⟨b,hb,he⟩ := max_witness ω ε A B W z
    apply (iInf_le_of_le b (iInf_le_of_le hb le_rfl)).trans
    have hh : value ≤ lin ω ε b v := (hm z hz).trans (he ▸ image_mono ω hω ε hε A B W z v hA hB hW b hb)
    change ((-lin ω ε b v : ℝ) : EReal) ≤ ((-value : ℝ) : EReal)
    exact_mod_cast neg_le_neg hh
  have hminbound : (⨆ v ∈ Y, F a v) ≤ (-value : ℝ) := by
    apply le_trans ?_ hupper
    rw [← heq]
    exact le_iInf fun b => le_iInf fun hb => hmin hb
  have hguarantee : ∀ z ∈ Z, value ≤ saddleObj ω ε A B W a z := by
    intro z hz
    let v : Fin 3 → ℝ := ![A z,B z,W z]
    have hv : v ∈ Y := ⟨z,hz,le_rfl,le_rfl,le_rfl⟩
    have hle : F a v ≤ ⨆ u ∈ Y, F a u := by
      apply le_iSup_of_le v
      apply le_iSup_of_le hv
      exact le_rfl
    have hh := hle.trans hminbound
    have he : lin ω ε a v = saddleObj ω ε A B W a z := by rfl
    change ((-lin ω ε a v : ℝ) : EReal) ≤ ((-value : ℝ) : EReal) at hh
    rw [he] at hh
    exact neg_le_neg_iff.mp (EReal.coe_le_coe_iff.mp hh)
  have hbound : ∀ b ∈ X, saddleObj ω ε A B W b z₀ ≤ value := by
    apply SaddleBalance.bound_by_three_samples ω hω ε A B W z₀ value
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hval : saddleObj ω ε A B W a z₀ = value := le_antisymm (hbound a ha) (hguarantee z₀ hz₀)
  refine ⟨a,ha,?_,?_⟩
  · intro z hz
    rw [hval]
    exact hguarantee z hz
  · intro b hb
    rw [hval]
    exact hbound b hb
end
end SaddleLift

section
theorem solution : (
  ∀ {E : Type u_1} [inst : AddCommGroup E]
    [inst_1 : @_root_.Module Real E Real.semiring (@AddCommGroup.toAddCommMonoid E inst)] [inst_2 : TopologicalSpace E]
    (ε : Real),
    @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) ε →
      ∀ (ω : Real → Real),
        Or (@Eq (Real → Real) ω PrivBayesTest.alphaTilde) (@Eq (Real → Real) ω (@id Real)) →
          ∀ (Z : Set E),
            @Convex Real E Real.semiring Real.partialOrder (@AddCommGroup.toAddCommMonoid E inst)
                (@SMulZeroClass.toSMul Real E
                  (@AddZero.toZero E
                    (@AddZeroClass.toAddZero E
                      (@AddMonoid.toAddZeroClass E
                        (@SubNegMonoid.toAddMonoid E (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))))
                  (@DistribSMul.toSMulZeroClass Real E
                    (@AddMonoid.toAddZeroClass E
                      (@SubNegMonoid.toAddMonoid E (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))
                    (@DistribMulAction.toDistribSMul Real E Real.instMonoid
                      (@SubNegMonoid.toAddMonoid E (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst)))
                      (@Module.toDistribMulAction Real E Real.semiring (@AddCommGroup.toAddCommMonoid E inst) inst_1))))
                Z →
              @Set.Nonempty E Z →
                ∀ (A B W : E → Real),
                  (∀ (z : E),
                      @Membership.mem E (Set E) (@Set.instMembership E) Z z →
                        @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                          (A z)) →
                    (∀ (z : E),
                        @Membership.mem E (Set E) (@Set.instMembership E) Z z →
                          @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                            (B z)) →
                      (∀ (z : E),
                          @Membership.mem E (Set E) (@Set.instMembership E) Z z →
                            @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                              (W z)) →
                        @ConvexOn Real E Real Real.semiring Real.partialOrder (@AddCommGroup.toAddCommMonoid E inst)
                            Real.instAddCommMonoid Real.partialOrder
                            (@SMulZeroClass.toSMul Real E
                              (@AddZero.toZero E
                                (@AddZeroClass.toAddZero E
                                  (@AddMonoid.toAddZeroClass E
                                    (@SubNegMonoid.toAddMonoid E
                                      (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))))
                              (@DistribSMul.toSMulZeroClass Real E
                                (@AddMonoid.toAddZeroClass E
                                  (@SubNegMonoid.toAddMonoid E
                                    (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))
                                (@DistribMulAction.toDistribSMul Real E Real.instMonoid
                                  (@SubNegMonoid.toAddMonoid E
                                    (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst)))
                                  (@Module.toDistribMulAction Real E Real.semiring (@AddCommGroup.toAddCommMonoid E inst)
                                    inst_1))))
                            (@instSMulOfMul Real Real.instMul) Z A →
                          @ConvexOn Real E Real Real.semiring Real.partialOrder (@AddCommGroup.toAddCommMonoid E inst)
                              Real.instAddCommMonoid Real.partialOrder
                              (@SMulZeroClass.toSMul Real E
                                (@AddZero.toZero E
                                  (@AddZeroClass.toAddZero E
                                    (@AddMonoid.toAddZeroClass E
                                      (@SubNegMonoid.toAddMonoid E
                                        (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))))
                                (@DistribSMul.toSMulZeroClass Real E
                                  (@AddMonoid.toAddZeroClass E
                                    (@SubNegMonoid.toAddMonoid E
                                      (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))
                                  (@DistribMulAction.toDistribSMul Real E Real.instMonoid
                                    (@SubNegMonoid.toAddMonoid E
                                      (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst)))
                                    (@Module.toDistribMulAction Real E Real.semiring
                                      (@AddCommGroup.toAddCommMonoid E inst) inst_1))))
                              (@instSMulOfMul Real Real.instMul) Z B →
                            @ConvexOn Real E Real Real.semiring Real.partialOrder (@AddCommGroup.toAddCommMonoid E inst)
                                Real.instAddCommMonoid Real.partialOrder
                                (@SMulZeroClass.toSMul Real E
                                  (@AddZero.toZero E
                                    (@AddZeroClass.toAddZero E
                                      (@AddMonoid.toAddZeroClass E
                                        (@SubNegMonoid.toAddMonoid E
                                          (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))))
                                  (@DistribSMul.toSMulZeroClass Real E
                                    (@AddMonoid.toAddZeroClass E
                                      (@SubNegMonoid.toAddMonoid E
                                        (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst))))
                                    (@DistribMulAction.toDistribSMul Real E Real.instMonoid
                                      (@SubNegMonoid.toAddMonoid E
                                        (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst)))
                                      (@Module.toDistribMulAction Real E Real.semiring
                                        (@AddCommGroup.toAddCommMonoid E inst) inst_1))))
                                (@instSMulOfMul Real Real.instMul) Z W →
                              @LowerSemicontinuousOn E Real inst_2 Real.instPreorder A Z →
                                @LowerSemicontinuousOn E Real inst_2 Real.instPreorder B Z →
                                  @LowerSemicontinuousOn E Real inst_2 Real.instPreorder W Z →
                                    (∀ (t : Real),
                                        @IsCompact E inst_2
                                          (@Set.ofPred E fun (z : E) =>
                                            And (@Membership.mem E (Set E) (@Set.instMembership E) Z z)
                                              (∀ (α : Real),
                                                @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                    (@Set.Icc Real Real.instPreorder
                                                      (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                                                      (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                                    α →
                                                  @LE.le Real Real.instLE (@PrivBayesTest.saddleObj E ω ε A B W α z)
                                                    t))) →
                                      And
                                        (∃ (α₀ : Real),
                                          And
                                            (@Membership.mem Real (Set Real) (@Set.instMembership Real)
                                              (@Set.Icc Real Real.instPreorder
                                                (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                                                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                              α₀)
                                            (∃ (z₀ : E),
                                              And (@Membership.mem E (Set E) (@Set.instMembership E) Z z₀)
                                                (And
                                                  (∀ (z : E),
                                                    @Membership.mem E (Set E) (@Set.instMembership E) Z z →
                                                      @LE.le Real Real.instLE (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)
                                                        (@PrivBayesTest.saddleObj E ω ε A B W α₀ z))
                                                  (∀ (α : Real),
                                                    @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                        (@Set.Icc Real Real.instPreorder
                                                          (@OfNat.ofNat Real (nat_lit 0)
                                                            (@Zero.toOfNat0 Real Real.instZero))
                                                          (@OfNat.ofNat Real (nat_lit 1)
                                                            (@One.toOfNat1 Real Real.instOne)))
                                                        α →
                                                      @LE.le Real Real.instLE (@PrivBayesTest.saddleObj E ω ε A B W α z₀)
                                                        (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)))))
                                        (∀ (α₀ : Real),
                                          @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                              (@Set.Icc Real Real.instPreorder
                                                (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                                                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                                              α₀ →
                                            ∀ (z₀ : E),
                                              @Membership.mem E (Set E) (@Set.instMembership E) Z z₀ →
                                                (∀ (z : E),
                                                    @Membership.mem E (Set E) (@Set.instMembership E) Z z →
                                                      @LE.le Real Real.instLE (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)
                                                        (@PrivBayesTest.saddleObj E ω ε A B W α₀ z)) →
                                                  (∀ (α : Real),
                                                      @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                          (@Set.Icc Real Real.instPreorder
                                                            (@OfNat.ofNat Real (nat_lit 0)
                                                              (@Zero.toOfNat0 Real Real.instZero))
                                                            (@OfNat.ofNat Real (nat_lit 1)
                                                              (@One.toOfNat1 Real Real.instOne)))
                                                          α →
                                                        @LE.le Real Real.instLE
                                                          (@PrivBayesTest.saddleObj E ω ε A B W α z₀)
                                                          (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)) →
                                                    And
                                                      (@Eq EReal (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀).toEReal
                                                        (⨆ (α : Real),
                                                          ⨆ (_ :
                                                            @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                              (@Set.Icc Real Real.instPreorder
                                                                (@OfNat.ofNat Real (nat_lit 0)
                                                                  (@Zero.toOfNat0 Real Real.instZero))
                                                                (@OfNat.ofNat Real (nat_lit 1)
                                                                  (@One.toOfNat1 Real Real.instOne)))
                                                              α),
                                                            ⨅ (z : E),
                                                              ⨅ (_ :
                                                                @Membership.mem E (Set E) (@Set.instMembership E) Z z),
                                                                (@PrivBayesTest.saddleObj E ω ε A B W α z).toEReal))
                                                      (@Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                          (@Set.Ioo Real Real.instPreorder
                                                            (@OfNat.ofNat Real (nat_lit 0)
                                                              (@Zero.toOfNat0 Real Real.instZero))
                                                            (@OfNat.ofNat Real (nat_lit 1)
                                                              (@One.toOfNat1 Real Real.instOne)))
                                                          α₀ →
                                                        ∃ (τ : Real),
                                                          And
                                                            (@Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                              (@Set.Icc Real Real.instPreorder
                                                                (@OfNat.ofNat Real (nat_lit 0)
                                                                  (@Zero.toOfNat0 Real Real.instZero))
                                                                (@OfNat.ofNat Real (nat_lit 1)
                                                                  (@One.toOfNat1 Real Real.instOne)))
                                                              τ)
                                                            (And
                                                              (@Eq Real (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)
                                                                (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                                                                  (A z₀)
                                                                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                                                    (@HMul.hMul Real Real Real
                                                                      (@instHMul Real Real.instMul) τ ε)
                                                                    (W z₀))))
                                                              (And
                                                                (@Eq Real (@PrivBayesTest.saddleObj E ω ε A B W α₀ z₀)
                                                                  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                                                                    (B z₀)
                                                                    (@HMul.hMul Real Real Real
                                                                      (@instHMul Real Real.instMul)
                                                                      (@HMul.hMul Real Real Real
                                                                        (@instHMul Real Real.instMul)
                                                                        (@HSub.hSub Real Real Real
                                                                          (@instHSub Real Real.instSub)
                                                                          (@OfNat.ofNat Real (nat_lit 1)
                                                                            (@One.toOfNat1 Real Real.instOne))
                                                                          τ)
                                                                        ε)
                                                                      (W z₀))))
                                                                (And
                                                                  (@Eq (Real → Real) ω PrivBayesTest.alphaTilde →
                                                                    @Ne Real α₀
                                                                        (@HDiv.hDiv Real Real Real
                                                                          (@instHDiv Real
                                                                            (@DivInvMonoid.toDiv Real
                                                                              Real.instDivInvMonoid))
                                                                          (@OfNat.ofNat Real (nat_lit 1)
                                                                            (@One.toOfNat1 Real Real.instOne))
                                                                          (@OfNat.ofNat Real (nat_lit 2)
                                                                            (@instOfNatAtLeastTwo Real (nat_lit 2)
                                                                              Real.instNatCast
                                                                              (@Nat.instAtLeastTwoHAddOfNat
                                                                                (@OfNat.ofNat Nat (nat_lit 1)
                                                                                  (instOfNatNat (nat_lit 1)))
                                                                                (@Nat.instNeZeroSucc
                                                                                  (@OfNat.ofNat Nat (nat_lit 0)
                                                                                    (instOfNatNat (nat_lit 0)))))))) →
                                                                      Or
                                                                        (@Eq Real τ
                                                                          (@OfNat.ofNat Real (nat_lit 0)
                                                                            (@Zero.toOfNat0 Real Real.instZero)))
                                                                        (@Eq Real τ
                                                                          (@OfNat.ofNat Real (nat_lit 1)
                                                                            (@One.toOfNat1 Real Real.instOne))))
                                                                  (@Eq (Real → Real) ω (@id Real) →
                                                                    @Eq Real τ
                                                                      (@OfNat.ofNat Real (nat_lit 1)
                                                                        (@One.toOfNat1 Real Real.instOne))))))))
) := by
  intro E instAdd instMod instTop ε hε ω hω Z hZ hZne A B W hA0 hB0 hW0 hAc hBc hWc hAl hBl hWl hcpt
  constructor
  · obtain ⟨z,hz,hm⟩ := SaddleBalance.minimax_attained Z hZne ε hε.le ω hω A B W hAl hBl hWl hcpt
    obtain ⟨a,ha,hmin,hmax⟩ := SaddleLift.dual_at_primal ε hε.le ω hω Z A B W hW0 hAc hBc hWc z hz hm
    exact ⟨a,ha,z,hz,hmin,hmax⟩
  · exact projected_consequences ε hε ω hω Z hZ hZne A B W hA0 hB0 hW0 hAc hBc hWc hAl hBl hWl hcpt
end
